module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparatedMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RightExactGlobalSectionsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentedPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparatedFinitePoints
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremQuasiFinite

/-!
# Serre's criterion for affineness of algebraic spaces

A quasi-compact and quasi-separated algebraic space is affine if and only if all higher
cohomology groups of its quasi-coherent modules vanish.

## Main results

* `RingHom.finiteType_of_forall_exists_eq_sum_mul`: a ring map `φ : A →+* B` is of finite type
  when the functions on a relation `p₁, p₂ : B →+* R` are sums of products from the two factors
  and relations along `p₂` descend to relations with coefficients from `A`.
* `AlgebraicGeometry.Space.exists_eq_sum_mul_of_isPullback_of_isSeparated_to_affine`: functions on
  the relation of a chart of a space separated over an affine scheme are sums of products of
  functions from the two projections.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_universallyInjective`: universally injective
  and locally of finite type implies locally quasi-finite.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_surjective_pullbackToGlobalFunctions`: a
  separated morphism to an affine object inducing a surjection on global functions, out of a
  quasi-compact space with right exact global sections, is locally of finite type.
* `AlgebraicGeometry.Space.isIso_toScheme_map_of_isQuasiAffine`: such a morphism, bijective on
  global functions, out of a space represented by a quasi-affine scheme `W`, induces an
  isomorphism of schemes from `W`.
* `AlgebraicGeometry.Space.isIso_hom_of_bijective_pullbackToGlobalFunctions`: a morphism to an
  affine object bijective on global functions, out of a quasi-compact, quasi-separated space with
  right exact global sections, is an isomorphism.
* `AlgebraicGeometry.Space.isAffineSpace_of_surjective_sectionsMap`: a quasi-compact,
  quasi-separated algebraic space with right exact global sections on quasi-coherent modules is
  affine.
* `AlgebraicGeometry.Space.isAffineSpace_iff_forall_isZero_rightDerived`: the criterion.

## References

* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 082J](https://stacks.math.columbia.edu/tag/082J)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Let `φ : A →+* B` and let `p₁, p₂ : B →+* R` be such that `R` is of finite type over `B`
through `p₁`, every element of `R` is a sum `∑ p₁(xᵢ) p₂(yᵢ)`, and every relation
`p₂(b) = ∑ p₁(rᵢ) p₂(μᵢ)` descends to a relation `b = ∑ φ(dᵢ) μᵢ` with coefficients from `A`.
Then `B` is of finite type over `A`. -/
theorem RingHom.finiteType_of_forall_exists_eq_sum_mul {A B R : Type*} [CommRing A] [CommRing B]
    [CommRing R] (φ : A →+* B) (p₁ p₂ : B →+* R) (hft : p₁.FiniteType)
    (hgen : ∀ z : R, ∃ (n : ℕ) (x y : Fin n → B), z = ∑ i, p₁ (x i) * p₂ (y i))
    (hdesc : ∀ (b : B) (n : ℕ) (μ r : Fin n → B), p₂ b = ∑ i, p₁ (r i) * p₂ (μ i) →
      ∃ d : Fin n → A, b = ∑ i, φ (d i) * μ i) :
    φ.FiniteType := by
  classical
  let := p₁.toAlgebra
  let := φ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  choose n x y hxy using hgen
  let G : Finset B := s.attach.biUnion fun e => Finset.univ.image (y e.1)
  have hG : Algebra.adjoin B (p₂ '' (G : Set B)) = ⊤ := by
    refine top_le_iff.1 (hs ▸ Algebra.adjoin_le fun e he => ?_)
    rw [hxy e]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Algebra.subset_adjoin ⟨y e i, ?_, rfl⟩)
    exact Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  refine ⟨⟨G, top_le_iff.1 fun b _ => ?_⟩⟩
  have hb : p₂ b ∈ Submodule.span B (Submonoid.closure (p₂ '' (G : Set B)) : Set R) := by
    rw [← Algebra.adjoin_eq_span, hG]
    trivial
  obtain ⟨k, c, m, hcm⟩ := Submodule.mem_span_set'.1 hb
  have hm : ∀ i, ∃ μ ∈ Submonoid.closure (G : Set B), p₂ μ = (m i : R) := by
    intro i
    have he : Submonoid.closure (p₂ '' (G : Set B)) =
        (Submonoid.closure (G : Set B)).map p₂.toMonoidHom :=
      (MonoidHom.map_mclosure p₂.toMonoidHom _).symm
    obtain ⟨μ, hμ, h⟩ : (m i : R) ∈ (Submonoid.closure (G : Set B)).map p₂.toMonoidHom :=
      he ▸ (m i).2
    exact ⟨μ, hμ, h⟩
  choose μ hμ hμm using hm
  obtain ⟨d, hd⟩ := hdesc b k μ c (by
    rw [← hcm]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, hμm]; rfl)
  rw [hd]
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  exact (Submonoid.closure_le (S := (Algebra.adjoin A (G : Set B)).toSubmonoid)).2
    Algebra.subset_adjoin (hμ i)

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X` be separated over an object `Y₀` of the site with affine underlying scheme, let
`φ : h_T ⟶ X` be a morphism from a representable presheaf with `T` affine, and let `R` with
`p₁, p₂ : R ⟶ T` represent `h_T ×_X h_T`. Then every function on `R` is a finite sum
`∑ p₁^*(xᵢ) p₂^*(yᵢ)` of products of functions pulled back from `T` along the two projections. -/
theorem exists_eq_sum_mul_of_isPullback_of_isSeparated_to_affine
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T R : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f) (φ : yoneda.obj T ⟶ X)
    {p₁ p₂ : R ⟶ T} (h : IsPullback (yoneda.map p₁) (yoneda.map p₂) φ φ)
    (z : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)) :
    ∃ (n : ℕ) (x y : Fin n → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
      z = ∑ i, ((BigFppfOver.toScheme B S hS).map p₁).appTop (x i) *
        ((BigFppfOver.toScheme B S hS).map p₂).appTop (y i) := by
  have _ := hY₀
  have _ := hT
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨t, ht⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (φ ≫ f)
  have hP : IsPullback (yoneda.map (pullback.fst t t)) (yoneda.map (pullback.snd t t))
      (yoneda.map t) (yoneda.map t) := (IsPullback.of_hasPullback t t).map yoneda
  have hw : p₁ ≫ t = p₂ ≫ t := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, ht, ← Category.assoc, ← Category.assoc, h.w])
  let ι : R ⟶ pullback t t := pullback.lift p₁ p₂ hw
  have hgc : (yoneda.map (pullback.fst t t) ≫ φ) ≫ f = (yoneda.map (pullback.snd t t) ≫ φ) ≫ f := by
    rw [Category.assoc, Category.assoc, ← ht, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition]
  let g : yoneda.obj (pullback t t) ⟶ pullback f f :=
    pullback.lift (yoneda.map (pullback.fst t t) ≫ φ) (yoneda.map (pullback.snd t t) ≫ φ) hgc
  have sq1 := Stacks.Spaces.isPullback_selfPullback_diagonal f φ ht.symm
  have sq : IsPullback (yoneda.map p₁ ≫ φ) (yoneda.map ι) (pullback.diagonal f) g := by
    refine sq1.of_iso h.isoPullback.symm (Iso.refl _) hP.isoPullback.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · refine hP.hom_ext ?_ ?_
      · simp only [Category.assoc, IsPullback.isoPullback_inv_fst, Iso.symm_hom,
          ← Functor.map_comp, ι, pullback.lift_fst]
      · simp only [Category.assoc, IsPullback.isoPullback_inv_snd, Iso.symm_hom,
          ← Functor.map_comp, ι, pullback.lift_snd]
    · simp
    · refine pullback.hom_ext ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Category.assoc, g,
          pullback.lift_fst]
        rw [← Category.assoc, hP.isoPullback_inv_fst]
      · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Category.assoc, g,
          pullback.lift_snd]
        rw [← Category.assoc, hP.isoPullback_inv_snd]
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι) :=
    hf.property g _ ι sq
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback t t)) :=
    IsAffine.of_isPullback ((IsPullback.of_hasPullback t t).map (BigFppfOver.toScheme B S hS))
  obtain ⟨w, rfl⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map ι)).2 z
  obtain ⟨n, x, y, hxy⟩ := CommRingCat.exists_eq_sum_mul_of_isPushout
    (isPushout_appTop_of_isPullback ((IsPullback.of_hasPullback t t).map
      (BigFppfOver.toScheme B S hS))) w
  refine ⟨n, x, y, ?_⟩
  rw [hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst,
    pullback.lift_snd]

attribute [local instance] pointTopology in
/-- A universally injective morphism locally of finite type is locally quasi-finite. -/
theorem isLocallyQuasiFinite_of_universallyInjective {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hui : UniversallyInjective B S hS f) :
    IsLocallyQuasiFinite B S hS f := by
  refine (isLocallyQuasiFinite_iff_forall_discreteTopology_fibre B S hS hX hY f hft).2
    fun p => ?_
  have := subsingleton_points_yoneda_fieldSpec B S hS p.carrier p.contained p.toBase
  have : Subsingleton (points B S hS (pullback (yonedaEquiv.symm p.value) f)) :=
    ⟨fun x y => hui _ (isAlgebraicSpace_yoneda B S hS _) _ (Subsingleton.elim _ _)⟩
  infer_instance

/-- The identity of an object of the site is an étale morphism of presheaves. -/
private theorem presheaf_inverseImage_etale_yoneda_map_id (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 U)) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
    (by rw [CategoryTheory.Functor.map_id]; infer_instance)

section RightExact

variable {B S hS} {Y : AlgebraicSpaces B S hS}
    (hY : ∀ ⦃M N : Modules.{u, u} B S hS Y.1 Y.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (q : Y ⟶ _root_.AlgebraicGeometry.schemeSpace T)
    (hq : Function.Surjective (pullbackToGlobalFunctions B S hS Y T q))

include hY hqc hq in
/-- A separated morphism to an affine object inducing a surjection on global functions is
locally of finite type, when its source is quasi-compact with right exact global sections on
quasi-coherent modules. -/
theorem isLocallyOfFiniteType_of_surjective_pullbackToGlobalFunctions
    (hsep : IsSeparated B S hS q.hom) : IsLocallyOfFiniteType B S hS q.hom := by
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).mp hqc
  have _ := hUaff
  have hid := presheaf_inverseImage_etale_yoneda_map_id B S hS U
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
    have h := haet U (yoneda.map (𝟙 U)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  let U₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a, haet'⟩
  have hU₀ : (SmallEtale.topology B S hS Y.1).CoversTop fun _ : PUnit.{u + 2} => U₀ :=
    SmallEtale.coversTop_of_isSurjective B S hS Y.1 Y.2 U₀
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 U a).1 hasurj)
  refine isLocallyOfFiniteType_of_exists_surjective_etale_source_chart B S hS
    ⟨U, a, hasurj, haet', ?_⟩
  let φ : U ⟶ T := yoneda.preimage (a ≫ q.hom)
  have hφ : yoneda.map φ = a ≫ q.hom := Functor.map_preimage _ _
  suffices hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map φ) by
    have h := (isLocallyOfFiniteType_yoneda_map_iff B S hS φ).2 hft
    rwa [hφ] at h
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  let c : _root_.AlgebraicGeometry.schemeSpace U ⟶ Y := ObjectProperty.homMk a
  have hc : IsAffineHom B S hS c.hom :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS a q.hom
      (hφ ▸ isAffineHom_yoneda_map B S hS φ) hsep
  have hrep := relativelyRepresentable_of_isAffineHom B S hS c hc
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback U₀.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS c hrep hc U₀ hUaff
  let p₁ : hrep.pullback U₀.1.hom ⟶ U := hrep.snd U₀.1.hom
  let p₂ : hrep.pullback U₀.1.hom ⟶ U := yoneda.preimage (hrep.fst U₀.1.hom)
  have hp₂ : yoneda.map p₂ = hrep.fst U₀.1.hom := Functor.map_preimage _ _
  have hpb : IsPullback (yoneda.map p₂) (yoneda.map p₁) a a :=
    hp₂ ▸ hrep.isPullback U₀.1.hom
  have hp₁et : Etale ((BigFppfOver.toScheme B S hS).map p₁) :=
    haet'.property a (hrep.fst U₀.1.hom) (hrep.snd U₀.1.hom) (hrep.isPullback U₀.1.hom)
  refine RingHom.finiteType_of_forall_exists_eq_sum_mul _
    ((BigFppfOver.toScheme B S hS).map p₁).appTop.hom
    ((BigFppfOver.toScheme B S hS).map p₂).appTop.hom
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance) (fun z => ?_) ?_
  · obtain ⟨n, x, y, hxy⟩ := exists_eq_sum_mul_of_isPullback_of_isSeparated_to_affine B S hS
      inferInstance hUaff hsep a hpb z
    exact ⟨n, y, x, hxy.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)⟩
  · intro b n μ r hb
    let pb := pullbackToGlobalFunctions B S hS (_root_.AlgebraicGeometry.schemeSpace U) U (𝟙 _)
    obtain ⟨d, hd⟩ := exists_eq_sum_mul_of_isAffineHom B S hS hY q hq c hc U₀ hU₀
      (fun i => pb (μ i)) r (pb b) (by
        change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (hrep.fst U₀.1.hom ≫ 𝟙 _))).op b = ∑ i,
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (hrep.fst U₀.1.hom ≫ 𝟙 _))).op (μ i) * _
        simp only
        refine hb.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _))
    refine ⟨d, ?_⟩
    let idChart : SmallEtale B S hS (_root_.AlgebraicGeometry.schemeSpace U).1 :=
      ⟨CostructuredArrow.mk (yoneda.map (𝟙 U)), hid⟩
    have hev := congrArg (globalFunctionsChartRestriction B S hS
      (_root_.AlgebraicGeometry.schemeSpace U) idChart) hd
    rw [map_sum] at hev
    have h1 : yoneda.preimage (yoneda.map (𝟙 U) ≫ 𝟙 (yoneda.obj U)) = 𝟙 U :=
      yoneda.map_injective (by rw [Functor.map_preimage, CategoryTheory.Functor.map_id,
        Category.id_comp])
    have h2 : yoneda.preimage (yoneda.map (𝟙 U) ≫ a ≫ q.hom) = φ := by
      refine yoneda.map_injective ?_
      rw [Functor.map_preimage, hφ, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (yoneda.map (𝟙 U) ≫ 𝟙 (yoneda.obj U)))).op b
        = ∑ i, globalFunctionsChartRestriction B S hS _ idChart
          (pullbackToGlobalFunctions B S hS _ T (c ≫ q) (d i) * pb (μ i)) at hev
    rw [h1] at hev
    simp only [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id] at hev
    refine hev.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul]
    change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (yoneda.map (𝟙 U) ≫ a ≫ q.hom))).op (d i) *
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (yoneda.map (𝟙 U) ≫ 𝟙 (yoneda.obj U)))).op (μ i) = _
    rw [h1, h2]
    simp only [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl

include hY hqc in
/-- Let `Y` be quasi-compact with right exact global sections on quasi-coherent modules,
represented by an object `W` of the site whose scheme is quasi-affine, and let `q : Y ⟶ T` induce
a bijection on global functions, `T` affine. Then the morphism of schemes `W ⟶ T` underlying `q`
is an isomorphism. -/
theorem isIso_toScheme_map_of_isQuasiAffine
    (hq' : Function.Bijective (pullbackToGlobalFunctions B S hS Y T q))
    {W : BigFppfOver B S hS} [hW : ((BigFppfOver.toScheme B S hS).obj W).IsQuasiAffine]
    (e : yoneda.obj W ≅ Y.1) :
    IsIso ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (e.hom ≫ q.hom))) := by
  let 𝒯 := BigFppfOver.toScheme B S hS
  let h : W ⟶ T := yoneda.preimage (e.hom ≫ q.hom)
  have hh : yoneda.map h = e.hom ≫ q.hom := Functor.map_preimage _ _
  have hid := presheaf_inverseImage_etale_yoneda_map_id B S hS W
  have _ := isMultiplicative_presheaf_etale B S hS
  have he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝒯).presheaf
      e.hom := by
    have h' := MorphismProperty.RespectsIso.postcomp _ e.hom _ hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h'
  let C₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk e.hom, he⟩
  let ι : Y ⟶ _root_.AlgebraicGeometry.schemeSpace W := ObjectProperty.homMk e.inv
  have hleft : ∀ x, globalFunctionsChartRestriction B S hS Y C₀
      (pullbackToGlobalFunctions B S hS Y W ι x) = x := by
    intro x
    change Scheme.Γ.map (𝒯.map (yoneda.preimage (e.hom ≫ e.inv))).op x = x
    rw [e.hom_inv_id, show yoneda.preimage (𝟙 (yoneda.obj W)) = 𝟙 W from
      yoneda.map_injective (by simp)]
    simp only [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  have hres : Function.Bijective (globalFunctionsChartRestriction B S hS Y C₀) :=
    ⟨injective_globalFunctionsChartRestriction_of_isSurjective B S hS Y C₀
      (pointsMap_surjective_of_isIso B S hS e.hom), fun x => ⟨_, hleft x⟩⟩
  have hΓ : Function.Bijective (𝒯.map h).appTop := hres.comp hq'
  have hΓiso : IsIso (𝒯.map h).appTop := (ConcreteCategory.isIso_iff_bijective _).2 hΓ
  have hfac : 𝒯.map h = (𝒯.obj W).toSpecΓ ≫ Spec.map (𝒯.map h).appTop ≫
      inv (𝒯.obj T).toSpecΓ := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion (𝒯.map h) := by
    rw [hfac]
    infer_instance
  have hpt : ∀ x : 𝒯.obj W, ∃ f : Γ(𝒯.obj T, ⊤), 𝒯.map h x ∈ (𝒯.obj T).basicOpen f ∧
      (𝒯.obj T).basicOpen f ≤ (𝒯.map h).opensRange := by
    intro x
    obtain ⟨V, ⟨f, rfl⟩, hxV, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen (𝒯.obj T))
        (show 𝒯.map h x ∈ (𝒯.map h).opensRange from Set.mem_range_self x)
    exact ⟨f, hxV, hVle⟩
  choose fx hfx₁ hfx₂ using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((𝒯.map h) ⁻¹ᵁ (𝒯.obj T).basicOpen (fx x) : (𝒯.obj W).Opens).1)
    (fun x => ((𝒯.map h) ⁻¹ᵁ (𝒯.obj T).basicOpen (fx x)).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hfx₁ x⟩)
  let f : Fin t.card → Γ(𝒯.obj T, ⊤) := fun j => fx (t.equivFin.symm j)
  have hf : ∀ x : 𝒯.obj W, ∃ j, 𝒯.map h x ∈ (𝒯.obj T).basicOpen (f j) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simp only [f, Equiv.symm_apply_apply]
    exact hxy
  obtain ⟨U₀, hU₀aff, hU₀⟩ := SmallEtale.exists_affineObject_coversTop B S hS Y.1 Y.2 hqc
  have hU₀aff' : IsAffine (𝒯.obj U₀.1.left) := hU₀aff
  let k : U₀.1.left ⟶ W := yoneda.preimage (U₀.1.hom ≫ e.inv)
  have hk : k ≫ h = yoneda.preimage (U₀.1.hom ≫ q.hom) := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, hh, Functor.map_preimage, Functor.map_preimage]
    change (U₀.1.hom ≫ e.inv) ≫ (e.hom ≫ q.hom : yoneda.obj W ⟶ (schemeSpace T).obj) =
      U₀.1.hom ≫ q.hom
    rw [Category.assoc, e.inv_hom_id_assoc]
  have hspan : Ideal.span (Set.range fun j => globalFunctionsChartRestriction B S hS Y U₀
      (pullbackToGlobalFunctions B S hS Y T q (f j))) = ⊤ := by
    rw [← (isAffineOpen_top (𝒯.obj U₀.1.left)).self_le_iSup_basicOpen_iff]
    intro u _
    obtain ⟨j, hj⟩ := hf (𝒯.map k u)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, ⟨j, rfl⟩⟩, ?_⟩
    change u ∈ (𝒯.obj U₀.1.left).basicOpen
      (Scheme.Γ.map (𝒯.map (yoneda.preimage (U₀.1.hom ≫ q.hom))).op (f j))
    rw [← hk, Functor.map_comp]
    change u ∈ (𝒯.obj U₀.1.left).basicOpen ((𝒯.map k ≫ 𝒯.map h).appTop (f j))
    rw [← Scheme.preimage_basicOpen_top]
    exact hj
  obtain ⟨y, hy⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hspan ▸ Submodule.mem_top :
    (1 : Γ(𝒯.obj U₀.1.left, ⊤)) ∈ _)
  obtain ⟨z, hz⟩ := exists_eq_sum_mul_of_surjective_sectionsMap B S hS hY U₀ hU₀ (n := 1)
    (fun _ => 1) (fun _ j => pullbackToGlobalFunctions B S hS Y T q (f j)) y (fun _ => by
      rw [map_one, ← hy]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
  choose d hd using fun j => hq'.2 (z j)
  have h1 : (1 : Γ(𝒯.obj T, ⊤)) = ∑ j, f j * d j := by
    refine hq'.1 ?_
    rw [map_one, map_sum, hz 0]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hd]
  have hcov := iSup_basicOpen_of_span_eq_top (⊤ : (𝒯.obj T).Opens) (Set.range f)
    ((Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2
      ⟨d, (h1.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)).symm⟩))
  have hrange : (𝒯.map h).opensRange = ⊤ := by
    refine top_unique fun y _ => ?_
    have hy' : y ∈ ⨆ i ∈ Set.range f, (𝒯.obj T).basicOpen i := by
      rw [hcov]
      trivial
    obtain ⟨_, ⟨j, rfl⟩, hyj⟩ : ∃ i ∈ Set.range f, y ∈ (𝒯.obj T).basicOpen i := by
      simpa [TopologicalSpace.Opens.mem_iSup] using hy'
    exact hfx₂ _ hyj
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ hrange

include hY hqc in
/-- Let `Y` be a quasi-compact, quasi-separated algebraic space over `S` with right exact
global sections on quasi-coherent modules, and let `q : Y ⟶ T` be a morphism to an affine object
of the site inducing a bijection `Γ(T) ≅ Γ(Y)` on global functions. Then `q` is an
isomorphism. -/
theorem isIso_hom_of_bijective_pullbackToGlobalFunctions (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hq' : Function.Bijective (pullbackToGlobalFunctions B S hS Y T q)) : IsIso q.hom := by
  have hsep : IsSeparated B S hS q.hom :=
    isSeparated_of_surjective_pullbackToGlobalFunctions hZ hY hqc hqs q hq'.2
  have hui := universallyInjective_of_surjective_pullbackToGlobalFunctions hZ hY hqc hqs q hq'.2
  have hft := isLocallyOfFiniteType_of_surjective_pullbackToGlobalFunctions hY hqc q hq'.2 hsep
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  have hlqf := isLocallyQuasiFinite_of_universallyInjective B S hS Y.2 hTalg q.hom hft hui
  have hTsep : IsAbsolutelySeparated B S hS hZ (yoneda.obj T) :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ T inferInstance (𝟙 _)
      (isSeparated_of_isIso B S hS (𝟙 _))
  have hqcq : IsQuasiCompact B S hS q.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hTalg
      (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _ hTsep) hqc q.hom
  have hqa := isQuasiAffineHom_of_isQuasiFinite_isSeparated Y.2 hTalg ⟨hlqf, hqcq⟩ hsep
  obtain ⟨W, hWqa, ⟨e₀⟩⟩ := hqa ⟨T, inferInstance⟩ (𝟙 _)
  have _ := hWqa
  have : IsIso (pullback.snd (𝟙 (yoneda.obj T)) q.hom) :=
    pullback_snd_iso_of_left_iso (𝟙 (yoneda.obj T)) q.hom
  let e : yoneda.obj W ≅ Y.1 := e₀ ≪≫ asIso (pullback.snd (𝟙 (yoneda.obj T)) q.hom)
  let h : W ⟶ T := yoneda.preimage (e.hom ≫ q.hom)
  have h𝒯 : IsIso ((BigFppfOver.toScheme B S hS).map h) :=
    isIso_toScheme_map_of_isQuasiAffine hY hqc q hq' e
  have hiso : IsIso h := isIso_of_reflects_iso h (BigFppfOver.toScheme B S hS)
  have hq : q.hom = e.inv ≫ yoneda.map h := by
    rw [Functor.map_preimage]
    change q.hom = e.inv ≫ (e.hom ≫ q.hom : yoneda.obj W ⟶ (schemeSpace T).obj)
    rw [Iso.inv_hom_id_assoc]
  have hc : IsIso (e.inv ≫ yoneda.map h) := inferInstance
  rw [hq]
  exact hc

end RightExact

/-- A quasi-compact, quasi-separated algebraic space with right exact global sections on
quasi-coherent modules is affine. -/
theorem isAffineSpace_of_surjective_sectionsMap (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    IsAffineSpace B S hS X.1 := by
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    ⟨viewOverIntegers B S hS hZ X.1,
      isAlgebraicSpace_relocalize B ⟨S, hS⟩ ⟨⊤_ Scheme.{u}, hZ⟩ k X.1 X.2⟩
  have hX' := surjective_sectionsMap_relocalize B S (⊤_ Scheme.{u}) hS hZ k X.2 X'.2 hX
  have hqc' : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X'.1 :=
    isQuasiCompactSpace_relocalize B S hS hZ k hqc
  have hqs' : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X'.1 :=
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X.1 hqs
  let M := (nonempty_globalFunctionsModel B (⊤_ Scheme.{u}) hZ X').some
  let p := toSpecGlobalFunctions B (⊤_ Scheme.{u}) hZ X' M terminalIsTerminal
  have hp : Function.Bijective (pullbackToGlobalFunctions B (⊤_ Scheme.{u}) hZ X'
      (specGlobalFunctions B (⊤_ Scheme.{u}) hZ X' M terminalIsTerminal) p) := by
    rw [pullbackToGlobalFunctions_toSpecGlobalFunctions]
    exact M.equiv.bijective.comp
      (Scheme.ΓSpecIso M.ring).commRingCatIsoToRingEquiv.bijective
  have hiso := isIso_hom_of_bijective_pullbackToGlobalFunctions hX' hqc' p hZ hqs' hp
  obtain ⟨e⟩ := OverShriek.nonempty_iso_yoneda_of_relocalize k X.1 (@asIso _ _ _ _ p.hom hiso)
  refine ⟨_, ?_, ⟨e⟩⟩
  exact isAffine_toScheme_obj_specGlobalFunctions B (⊤_ Scheme.{u}) hZ X' M terminalIsTerminal

section Criterion

open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- A quasi-compact and quasi-separated algebraic space is affine if and only if all higher
cohomology groups of its quasi-coherent modules vanish. Cohomology is that of `𝒪_X`-modules on
the small étale site, for modules whose sections lie in the universe of the structure sheaf. -/
theorem isAffineSpace_iff_forall_isZero_rightDerived (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsAffineSpace B S hS X.1 ↔
      ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite → ∀ i : ℕ, 0 < i →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine ⟨fun ⟨V, hV, ⟨e⟩⟩ F hF i hi => ?_, fun h => ?_⟩
  · let f : X ⟶ _root_.AlgebraicGeometry.schemeSpace V := ObjectProperty.homMk e.hom
    have hf : IsAffineHom B S hS f.hom := isAffineHom_of_isIso e.hom
    have := hasInjectiveResolutions_modules B S hS (_root_.AlgebraicGeometry.schemeSpace V).1
      (_root_.AlgebraicGeometry.schemeSpace V).2
    exact isZero_of_faithful (forget₂ _ AddCommGrpCat.{u + 1})
      ((Functor.map_isZero (forget₂ _ AddCommGrpCat.{u + 1})
        (isZero_rightDerived_globalSectionsFunctor_of_isAffine B S hS V hV _
          (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' f hf hF) i hi)).of_iso
        (cohomologyIsoOfIsAffineHom B S hS f hf F hF i))
  · refine isAffineSpace_of_surjective_sectionsMap B S hS hZ (fun M N g hg hM hN => ?_) hqc hqs
    have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
    have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS X.1 X.2
    have hQ : (ShortComplex.mk (SheafOfModules.Submodule.ker g).ι g
        (SheafOfModules.Submodule.ker_ι_comp _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _
          (SheafOfModules.Submodule.isLimitKernelFork _)
        mono_f := mono_of_isLimit_fork (SheafOfModules.Submodule.isLimitKernelFork _)
        epi_g := hg }
    have hK : (SheafOfModules.Submodule.ker g).toSheafOfModules.IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.Submodule.kerIsoKernel g).symm
        ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel g hM hN)
    exact (ModuleCat.epi_iff_surjective _).1
      (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one _ hQ (h _ hK 1 one_pos))

end Criterion

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleIrreducibleCover0551c
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres
public import StacksFrontier.RingTheory.Etale.IntegralSplitting

/-!
# Splitting the Stein factorization after an étale base change

This is a helper module of the proof of Stacks 0E0D. Its declarations live in the
`AlgebraicGeometry.ProperFlatStein` and `AlgebraicGeometry.Space.ProperFlatStein` namespaces;
it records no tag.

This file carries out the first step of the proof of Stacks 0E0D.  Let `f = f' ≫ π` with
`π : Y' ⟶ Y` integral, `f` quasi-compact and locally of finite type, and the geometric fibres
of `f'` connected.  Given a point `y` of `|Y|` there is an affine étale chart `U₀ ⟶ Y` through
`y` over which `π` becomes a morphism of affine schemes `T₀ ⟶ U₀` which splits, by idempotents,
into pieces each having exactly one point over a chosen lift `u₀` of `y`, with purely
inseparable residue field extension.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.isSurjective_of_connectedPullback`: a morphism all of
  whose geometric
  fibres are connected is surjective, connected spaces being nonempty.
* `AlgebraicGeometry.Space.ProperFlatStein.exists_split_affine_chart`: the first step of the proof
  of Stacks 0E0D.
  For `f' : X ⟶ Y'` surjective and `π : Y' ⟶ Y` integral with `f' ≫ π` quasi-compact and locally
  of finite type, every point `y` of `Y` lies under a point `z₀` of an affine étale chart
  `U₀ ⟶ Y` over which `π` is an integral morphism of affine schemes `T₀ ⟶ U₀`, and `T₀` is
  covered by finitely many open and closed affine pieces `V i`, each having exactly one point
  over `z₀`, with purely inseparable residue field extension.

## Implementation notes

The chart `U₀` is produced in three steps.  Stacks 0E1C, in its scheme-level form
`AlgebraicGeometry.finite_preimage_singleton_of_surjective_of_locallyOfFiniteType` and
`AlgebraicGeometry.finite_residueFieldMap_of_surjective_of_locallyOfFiniteType`, shows that the
integral morphism `T' ⟶ W` obtained by testing `π` at an affine étale chart `W` through `y` has
finite fibres and finite residue field extensions.  Read on global sections, this is exactly the
input of Stacks 0BSR,
`Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable`, which
produces the étale algebra `R₂` and the idempotents of `R₂ ⊗ Γ(T')`.  Finally `Spec R₂`,
`Spec (R₂ ⊗ Γ(T'))` and the localizations at the idempotents are made objects of the site with
`AlgebraicGeometry.BigFppfOver.siteObjectOver`, all of them being affine and locally of finite
presentation over objects already in the site.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
* [Stacks Project, Tag 0E1C](https://stacks.math.columbia.edu/tag/0E1C)
* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ProperFlatStein

/-! ### Residue fields of a morphism of spectra -/

/-- A prime of `S` over which `Spec` of an algebra map sends a prime `t` to `z` lies over `z`. -/
private theorem liesOver_of_specMap_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {t : PrimeSpectrum S} {z : PrimeSpectrum R}
    (hz : Spec.map (CommRingCat.ofHom (algebraMap R S)) t = z) : t.asIdeal.LiesOver z.asIdeal :=
  ⟨by rw [← hz]; rfl⟩

/-- `Spec` of an algebra map sends a prime `t` lying over `z` to `z`. -/
private theorem specMap_eq_of_liesOver {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (t : PrimeSpectrum S) (z : PrimeSpectrum R) [h : t.asIdeal.LiesOver z.asIdeal] :
    Spec.map (CommRingCat.ofHom (algebraMap R S)) t = z :=
  PrimeSpectrum.ext h.over.symm

/-- **The residue field map of `Spec` of an algebra map is the algebra map of residue fields.**
Read through `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, the map of residue fields of
`Spec S ⟶ Spec R` at a prime `t` over `z` is the algebra map `κ(z) ⟶ κ(t)` defined by
`Localization.AtPrime.algebraOfLiesOver`. -/
private theorem algebraMap_residueField_eq_residueFieldMap {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (t : PrimeSpectrum S) (z : PrimeSpectrum R)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap R S)) t = z) [t.asIdeal.LiesOver z.asIdeal] :
    letI := Localization.AtPrime.algebraOfLiesOver z.asIdeal t.asIdeal
    algebraMap z.asIdeal.ResidueField t.asIdeal.ResidueField =
      ((Scheme.Spec.residueFieldIso (.of R) z).inv ≫
        ((Spec (.of R)).residueFieldCongr hz).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap t ≫
            (Scheme.Spec.residueFieldIso (.of S) t).hom).hom := by
  let := Localization.AtPrime.algebraOfLiesOver z.asIdeal t.asIdeal
  have h := congrArg CommRingCat.Hom.hom
    (algebraMap_Spec_map_residueFieldMap (CommRingCat.ofHom (algebraMap R S)) t z hz)
  refine Ideal.ResidueField.ringHom_ext ?_
  ext r
  have hr := DFunLike.congr_fun h r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hr ⊢
  rw [hr]
  simp [← IsScalarTower.algebraMap_apply]

/-- A ring map of fields which becomes purely inseparable after composing with isomorphisms on
both sides is purely inseparable. -/
private theorem isPurelyInseparable_of_comp_ringEquiv {K K' L L' : Type u} [Field K] [Field K']
    [Field L] [Field L'] (e₁ : K' ≃+* K) (f : K →+* L) (e₂ : L ≃+* L')
    (h : (e₂.toRingHom.comp (f.comp e₁.toRingHom)).IsPurelyInseparable) :
    f.IsPurelyInseparable := by
  have hf : f = e₂.symm.toRingHom.comp
      ((e₂.toRingHom.comp (f.comp e₁.toRingHom)).comp e₁.symm.toRingHom) := by
    ext x
    simp
  rw [hf]
  exact (RingHom.isPurelyInseparable_of_surjective _ e₁.symm.surjective).comp h |>.comp
    (RingHom.isPurelyInseparable_of_surjective _ e₂.symm.surjective)

/-- A ring map which becomes finite after composing with isomorphisms on both sides is
finite. -/
private theorem finite_of_isIso_comp {K K' L L' : CommRingCat.{u}} (g₁ : K' ⟶ K) [IsIso g₁]
    (f : K ⟶ L) (g₂ : L ⟶ L') [IsIso g₂] (h : f.hom.Finite) : (g₁ ≫ f ≫ g₂).hom.Finite := by
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso g₂).surjective).comp h |>.comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso g₁).surjective)

/-- Pure inseparability of the residue field extension `κ(z) ⟶ κ(t)` of a prime `t` over `z`
gives pure inseparability of the residue field map of `Spec` of the algebra map at `t`. -/
private theorem isPurelyInseparable_residueFieldMap_specMap {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (t : PrimeSpectrum S) (z : PrimeSpectrum R)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap R S)) t = z) [t.asIdeal.LiesOver z.asIdeal]
    (h : letI := Localization.AtPrime.algebraOfLiesOver z.asIdeal t.asIdeal
      IsPurelyInseparable z.asIdeal.ResidueField t.asIdeal.ResidueField) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap
      t).hom.IsPurelyInseparable := by
  let := Localization.AtPrime.algebraOfLiesOver z.asIdeal t.asIdeal
  have hp := RingHom.isPurelyInseparable_algebraMap_iff.mpr h
  rw [algebraMap_residueField_eq_residueFieldMap t z hz] at hp
  let : Field ((Spec (.of S)).residueField t) :=
    Scheme.instFieldCarrierResidueField (Spec (.of S)) t
  exact isPurelyInseparable_of_comp_ringEquiv
    ((Scheme.Spec.residueFieldIso _ _).symm ≪≫
      ((Spec _).residueFieldCongr hz).symm).commRingCatIsoToRingEquiv _
    (Scheme.Spec.residueFieldIso _ _).commRingCatIsoToRingEquiv hp

/-! ### Stacks 0BSR on spectra -/

/-- The spectra of the localizations at a complete family of orthogonal idempotents cover the
spectrum. -/
theorem exists_mem_range_comap_away_of_completeOrthogonalIdempotents {A : Type u} [CommRing A]
    {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e) (t : PrimeSpectrum A) :
    ∃ i, t ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (e i)))) := by
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ t.asIdeal := by
    by_contra h
    push Not at h
    have h1 : (1 : A) ∈ t.asIdeal := he.complete ▸ Ideal.sum_mem _ fun i _ => h i
    exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact ⟨i, by rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away (e i)) (e i)]⟩

/-- **Stacks 0E1C, read on global sections.** If `g : U ⟶ X` is surjective with `U`
quasi-compact, `p : X ⟶ Y` is integral between affine schemes and `g ≫ p` is locally of finite
type, then `Spec` of `p` on global sections has finite fibres and finite residue field maps. -/
theorem finite_specMap_appTop_of_surjective_of_locallyOfFiniteType {U X Y : Scheme.{u}}
    (g : U ⟶ X) (p : X ⟶ Y) [IsAffine X] [IsAffine Y] [CompactSpace U] [IsIntegralHom p]
    [LocallyOfFiniteType (g ≫ p)] (hg : Function.Surjective g) :
    (∀ x, (Spec.map p.appTop ⁻¹' {x}).Finite) ∧
      ∀ t, ((Spec.map p.appTop).residueFieldMap t).hom.Finite := by
  have : IsIntegralHom (Spec.map p.appTop) :=
    IsIntegralHom.SpecMap_iff.mpr (p.isIntegral_app ⊤ (isAffineOpen_top _))
  have : LocallyOfFiniteType ((g ≫ X.isoSpec.hom) ≫ Spec.map p.appTop) := by
    rw [Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc]
    infer_instance
  have : Surjective g := ⟨hg⟩
  have hg' : Function.Surjective (g ≫ X.isoSpec.hom) :=
    (inferInstance : Surjective (g ≫ X.isoSpec.hom)).surj
  exact ⟨finite_preimage_singleton_of_surjective_of_locallyOfFiniteType _ _ hg',
    finite_residueFieldMap_of_surjective_of_locallyOfFiniteType _ _ hg'⟩

/-- **Stacks 0BSR, read on spectra.** Let `φ : R ⟶ S` be integral and let `x` be a prime of `R`
such that `Spec φ` has finitely many points over `x` and finite residue field extensions.  Then
there is an étale `R`-algebra `R₂` with a prime `u` over `x` such that `Spec (R₂ ⊗[R] S)` is
covered by finitely many open and closed affine pieces `Spec (L i)`, each having exactly one
point over `u`, with purely inseparable residue field extension. -/
private theorem exists_split_spec {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.IsIntegral)
    (x : PrimeSpectrum R) (hfin : ((Spec.map φ) ⁻¹' {x}).Finite)
    (hres : ∀ t, ((Spec.map φ).residueFieldMap t).hom.Finite) :
    ∃ (R₂ A : CommRingCat.{u}) (a : R ⟶ R₂) (i₁ : R₂ ⟶ A) (i₂ : S ⟶ A),
      IsPushout φ a i₂ i₁ ∧ a.hom.Etale ∧ ∃ u : Spec R₂, Spec.map a u = x ∧
      ∃ (n : ℕ) (L : Fin n → CommRingCat.{u}) (l : ∀ i, A ⟶ L i),
        (∀ i, IsOpenImmersion (Spec.map (l i))) ∧ (∀ i, IsClosedImmersion (Spec.map (l i))) ∧
        (∀ t : Spec A, ∃ i, t ∈ Set.range (Spec.map (l i))) ∧
        ∀ i, ∃ v : Spec (L i), (Spec.map (i₁ ≫ l i)) ⁻¹' {u} = {v} ∧
          ((Spec.map (i₁ ≫ l i)).residueFieldMap v).hom.IsPurelyInseparable := by
  let : Algebra R S := φ.hom.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hφ⟩
  have hfinite : Set.Finite {q : Ideal S | q.IsPrime ∧ q.LiesOver x.asIdeal} := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro q ⟨hq, hqo⟩
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqo.over.symm, rfl⟩
  have hsep : ∀ (q : Ideal S) (hq : q.IsPrime) (hqover : q.LiesOver x.asIdeal),
      let := hq
      let := hqover
      let := Localization.AtPrime.algebraOfLiesOver x.asIdeal q
      Module.Finite x.asIdeal.ResidueField
        (separableClosure x.asIdeal.ResidueField q.ResidueField) := by
    intro q hq hqover
    let := Localization.AtPrime.algebraOfLiesOver x.asIdeal q
    let t : PrimeSpectrum S := ⟨q, hq⟩
    have hfin' : Module.Finite x.asIdeal.ResidueField q.ResidueField := by
      rw [← RingHom.finite_algebraMap, algebraMap_residueField_eq_residueFieldMap t x
        (PrimeSpectrum.ext hqover.over.symm), ← Category.assoc]
      exact finite_of_isIso_comp _ _ _ (hres t)
    infer_instance
  obtain ⟨R₂, _, _, _, p₂, _, _, n, e, he, r, hr, hrover, -, huniq, hpure⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable
      x.asIdeal hfinite hsep
  refine ⟨.of R₂, .of (R₂ ⊗[R] S), CommRingCat.ofHom (algebraMap R R₂),
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom,
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom,
    (CommRingCat.isPushout_tensorProduct R R₂ S).flip, RingHom.etale_algebraMap.mpr inferInstance,
    ⟨p₂, inferInstance⟩, specMap_eq_of_liesOver _ _, n,
    fun i => .of (Localization.Away (e i)), fun i => CommRingCat.ofHom (algebraMap _ _),
    fun i => inferInstance,
    fun i => IsClosedImmersion.spec_of_surjective _
      (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (e i) (he.idem i)), ?_, ?_⟩
  · exact exists_mem_range_comap_away_of_completeOrthogonalIdempotents he
  · intro i
    beta_reduce
    have hψ : (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          R₂ →+* R₂ ⊗[R] S) ≫
        CommRingCat.ofHom (algebraMap (R₂ ⊗[R] S) (Localization.Away (e i)))) =
        CommRingCat.ofHom (algebraMap R₂ (Localization.Away (e i))) := by
      ext r
      simp [IsScalarTower.algebraMap_apply R₂ (R₂ ⊗[R] S) (Localization.Away (e i))]
    rw [hψ]
    let v : PrimeSpectrum (Localization.Away (e i)) := ⟨r i, hr i⟩
    let u : PrimeSpectrum R₂ := ⟨p₂, inferInstance⟩
    have : v.asIdeal.LiesOver p₂ := hrover i
    have hvu := specMap_eq_of_liesOver v u
    refine ⟨v, ?_, ?_⟩
    · ext q
      simp only [Set.mem_preimage]
      refine ⟨fun hq => PrimeSpectrum.ext (huniq i q.asIdeal q.isPrime (liesOver_of_specMap_eq hq)),
        ?_⟩
      rintro rfl
      exact hvu
    · let := Localization.AtPrime.algebraOfLiesOver p₂ (r i)
      exact isPurelyInseparable_residueFieldMap_specMap v u hvu (hpure i)

end AlgebraicGeometry.ProperFlatStein

namespace AlgebraicGeometry.Space.ProperFlatStein

open AlgebraicGeometry.ProperFlatStein

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ProperFlatSteinSplitting
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Let `s : X ⟶ T'` be a morphism of presheaves to a representable one, surjective on points,
and `p : T' ⟶ T` a morphism of the site with `T` affine, such that `s ≫ p` is quasi-compact and
locally of finite type.  Then `X` has a surjective étale chart whose scheme `U` is compact, and
the induced `U ⟶ T'` is surjective with `U ⟶ T` locally of finite type.  This is the argument of
the private `exists_compact_chart_scheme_data` of
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres`, for a representable
target. -/
private theorem exists_compact_chart_over_affine {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T T' : BigFppfOver B S hS} (s : X ⟶ yoneda.obj T') (p : T' ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hsurj : IsSurjective B S hS s)
    (hqc : IsQuasiCompact B S hS (s ≫ yoneda.map p))
    (hlft : IsLocallyOfFiniteType B S hS (s ≫ yoneda.map p)) :
    ∃ (U : BigFppfOver B S hS) (g : U ⟶ T'),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map g) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g ≫
        (BigFppfOver.toScheme B S hS).map p) := by
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS T)
      (isAffineSpace_yoneda B S hS T hT).isQuasiCompactSpace hqc
  obtain ⟨U, a, hUcpt, hasurj, haetale⟩ := hXqc
  have hgmap : yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ s)) = a ≫ s :=
    Yoneda.fullyFaithful.map_preimage _
  refine ⟨U, Yoneda.fullyFaithful.preimage (a ≫ s), hUcpt, ?_, ?_⟩
  · have hpts : Function.Surjective (pointsMap B S hS (yoneda.obj U)
        (yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ s)))) := by
      rw [hgmap, pointsMap_comp]
      exact hsurj.comp (isSurjective_of_presheafSurjective B S hS a hasurj)
    have hsurj' : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
        (Yoneda.fullyFaithful.preimage (a ≫ s))) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).mp
        ((surjective_yonedaMap_iff_surjective_pointsMap B S hS _).mpr hpts)
    exact (AlgebraicGeometry.surjective_iff _).mp hsurj'
  · have h0 : MorphismProperty.ContainsIdentities
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have h1 : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have h2 : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    have hbet : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) :=
      MorphismProperty.presheaf_of_isIso _ _
    have hsq2 : yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ s) ≫ p) ≫ 𝟙 (yoneda.obj T) =
        a ≫ (s ≫ yoneda.map p) := by
      rw [CategoryTheory.Functor.map_comp, hgmap, Category.comp_id, Category.assoc]
    have := hlft U T a (𝟙 _) (Yoneda.fullyFaithful.preimage (a ≫ s) ≫ p)
      (presheaf_etale_of_isEtale B S hS haetale) hbet hsq2
    rwa [CategoryTheory.Functor.map_comp] at this

/-- A morphism of presheaves on the big fppf site all of whose geometric fibres have connected,
hence nonempty, point spaces is surjective on points. -/
theorem isSurjective_of_connectedPullback {X Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f' : X ⟶ Y')
    (hconn : ∀ y' : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y'.val.value)) :
    IsSurjective B S hS f' := by
  intro y
  obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS Y' y
  obtain ⟨z⟩ := (hconn p).toNonempty
  refine ⟨pointsMap B S hS _ (pullback.fst f' (yonedaEquiv.symm p.val.value)) z, ?_⟩
  rw [pointsMap_apply_comm B S hS pullback.condition z]
  exact (FieldValuedPoint.pointsMap_eq_class B S hS p.val _).trans hp

/-- A square of the site whose image in schemes is cartesian, with its top edge given only as a
morphism of schemes `qS`, lifts to a cartesian square of the site. -/
theorem exists_isPullback_of_isPullback_toScheme_map {U₀ T₀ W T' : BigFppfOver B S hS}
    (p : T' ⟶ W) (a₀ : U₀ ⟶ W) (p₀ : T₀ ⟶ U₀)
    {qS : (BigFppfOver.toScheme B S hS).obj T₀ ⟶ (BigFppfOver.toScheme B S hS).obj T'}
    (h : IsPullback qS ((BigFppfOver.toScheme B S hS).map p₀) ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map a₀)) :
    ∃ q₀ : T₀ ⟶ T', (BigFppfOver.toScheme B S hS).map q₀ = qS ∧ IsPullback q₀ p₀ p a₀ := by
  have hv : qS ≫ B.inclusion.map T'.hom = B.inclusion.map T₀.hom := by
    have h' := congrArg (· ≫ B.inclusion.map W.hom) h.w
    simp only [Category.assoc] at h'
    rw [← Over.w p, ← Over.w p₀, ← Over.w a₀]
    simp only [Functor.map_comp]
    exact h'
  refine ⟨BigFppfOver.homOfCompEq B S hS qS hv, BigFppfOver.toScheme_map_homOfCompEq B S hS qS hv,
    IsPullback.of_map (BigFppfOver.toScheme B S hS)
      ((BigFppfOver.toScheme B S hS).map_injective ?_) ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact h.w
  · rwa [BigFppfOver.toScheme_map_homOfCompEq]

/-- A point `u` of `Spec R` over the image of a point `w` of an affine object `W` of the site,
along `Spec` of a map `a : Γ(W) ⟶ R`, is a point of the site object `Spec R ⟶ W` over `w`. -/
theorem exists_pointsMap_siteMapOver_eq {W : BigFppfOver B S hS} {R : CommRingCat.{u}}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (a : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ⟶ R) (hR : B.Contains (Spec R))
    (w : points B S hS (yoneda.obj W)) (u : Spec R)
    (hu : Spec.map a u =
      ((BigFppfOver.toScheme B S hS).obj W).isoSpec.hom (pointsToScheme B S hS W w)) :
    ∃ z, pointsToScheme B S hS (BigFppfOver.siteObjectOver B S hS W hR
        (Spec.map a ≫ ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv)) z = u ∧
      pointsMap B S hS _ (yoneda.map (BigFppfOver.siteMapOver B S hS W hR
        (Spec.map a ≫ ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv))) z = w := by
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS (BigFppfOver.siteObjectOver B S hS W hR
    (Spec.map a ≫ ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv)) u
  refine ⟨z, hz, injective_pointsToScheme B S hS W ?_⟩
  rw [pointsToScheme_pointsMap_yoneda, hz]
  change ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv (Spec.map a u) =
    pointsToScheme B S hS W w
  rw [hu, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- **Stacks 0BSR in the site.** Let `p : T' ⟶ W` be a morphism of the site between affine
objects which is integral, such that `Spec` of `p` on global sections has finite fibres and finite
residue field maps.  Then every point `w` of `W` is the image of a point `z₀` of an affine étale
`a₀ : U₀ ⟶ W` such that the base change `p₀ : T₀ ⟶ U₀` of `p` is covered by finitely many affine
pieces `V i`, open and closed in `T₀`, each of which has exactly one point `v` over `z₀`, with
`κ(v)` purely inseparable over `κ(z₀)`. -/
theorem exists_split_affine_chart_of_isAffine {W T' : BigFppfOver B S hS} (p : T' ⟶ W)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    [_root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p)]
    (w : points B S hS (yoneda.obj W))
    (hfin : ∀ x, (Spec.map ((BigFppfOver.toScheme B S hS).map p).appTop ⁻¹' {x}).Finite)
    (hres : ∀ t,
      ((Spec.map ((BigFppfOver.toScheme B S hS).map p).appTop).residueFieldMap t).hom.Finite) :
    ∃ (U₀ T₀ : BigFppfOver B S hS) (a₀ : U₀ ⟶ W) (p₀ : T₀ ⟶ U₀) (q₀ : T₀ ⟶ T')
      (z₀ : points B S hS (yoneda.obj U₀)) (n : ℕ)
      (V : Fin n → BigFppfOver B S hS) (ι : ∀ i, V i ⟶ T₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map a₀) ∧
      IsPullback q₀ p₀ p a₀ ∧
      _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p₀) ∧
      pointsMap B S hS (yoneda.obj U₀) (yoneda.map a₀) z₀ = w ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
        ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      ∀ i, ∃ v : (BigFppfOver.toScheme B S hS).obj (V i),
        ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀)) ⁻¹' {pointsToScheme B S hS U₀ z₀} = {v} ∧
        ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀)
          |>.residueFieldMap v).hom.IsPurelyInseparable := by
  let φ := ((BigFppfOver.toScheme B S hS).map p).appTop
  -- Stacks 0BSR.
  obtain ⟨R₂, A, a, i₁, i₂, hpo, ha, u, hu, n, L, l, hopen, hclosed, hcover, hpiece⟩ :=
    exists_split_spec φ (((BigFppfOver.toScheme B S hS).map p).isIntegral_app ⊤
      (isAffineOpen_top _))
      (((BigFppfOver.toScheme B S hS).obj W).isoSpec.hom (pointsToScheme B S hS W w)) (hfin _) hres
  -- The étale chart `U₀ = Spec R₂` of `W`, and the base change `T₀ = Spec A` of `T'`.
  have : _root_.AlgebraicGeometry.Etale (Spec.map a) := HasRingHomProperty.Spec_iff.mpr ha
  have hsqS : IsPullback (Spec.map i₂) (Spec.map i₁) (Spec.map φ) (Spec.map a) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have : LocallyOfFinitePresentation (Spec.map i₂) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsqS.flip inferInstance
  let aS : Spec R₂ ⟶ (BigFppfOver.toScheme B S hS).obj W :=
    Spec.map a ≫ ((BigFppfOver.toScheme B S hS).obj W).isoSpec.inv
  let qS : Spec A ⟶ (BigFppfOver.toScheme B S hS).obj T' :=
    Spec.map i₂ ≫ ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv
  have hU₀c : B.Contains (Spec R₂) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B aS W.left.property
  have hT₀c : B.Contains (Spec A) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B qS T'.left.property
  let U₀ := BigFppfOver.siteObjectOver B S hS W hU₀c aS
  let a₀ : U₀ ⟶ W := BigFppfOver.siteMapOver B S hS W hU₀c aS
  let T₀ := BigFppfOver.siteObjectOver B S hS U₀ hT₀c (Spec.map i₁)
  let p₀ : T₀ ⟶ U₀ := BigFppfOver.siteMapOver B S hS U₀ hT₀c (Spec.map i₁)
  have hschemeSq : IsPullback qS (Spec.map i₁) ((BigFppfOver.toScheme B S hS).map p) aS :=
    hsqS.of_iso (Iso.refl _) ((BigFppfOver.toScheme B S hS).obj T').isoSpec.symm (Iso.refl _)
      ((BigFppfOver.toScheme B S hS).obj W).isoSpec.symm (by simp [qS]) (by simp)
      (Scheme.isoSpec_inv_naturality _) (by simp [aS])
  obtain ⟨q₀, -, hsite⟩ :=
    exists_isPullback_of_isPullback_toScheme_map B S hS p a₀ p₀ hschemeSq
  -- The pieces `V i = Spec (L i)` of `T₀`.
  have hVc : ∀ i, B.Contains (Spec (L i)) := fun i => by
    have := hopen i
    exact BigFppfSite.contains_of_locallyOfFinitePresentation B (Spec.map (l i)) hT₀c
  let V : Fin n → BigFppfOver B S hS := fun i =>
    BigFppfOver.siteObjectOver B S hS T₀ (hVc i) (Spec.map (l i))
  let ι : ∀ i, V i ⟶ T₀ := fun i =>
    BigFppfOver.siteMapOver B S hS T₀ (hVc i) (Spec.map (l i))
  -- The point `z₀` of `U₀` over `w`.
  obtain ⟨z₀, rfl, hz₀⟩ := exists_pointsMap_siteMapOver_eq B S hS a hU₀c w u hu
  refine ⟨U₀, T₀, a₀, p₀, q₀, z₀, n, V, ι, (inferInstance : IsAffine (Spec R₂)),
    (inferInstance : IsAffine (Spec A)),
    (presheaf_yoneda_map_etale_iff B S hS a₀).2
      (inferInstance : _root_.AlgebraicGeometry.Etale aS), hsite,
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsIntegralHom)
      hschemeSq inferInstance, hz₀,
    fun i => (inferInstance : IsAffine (Spec (L i))), hopen, hclosed, hcover, fun i => ?_⟩
  obtain ⟨v, hv⟩ := hpiece i
  have hmap : (BigFppfOver.toScheme B S hS).map (ι i ≫ p₀) = Spec.map (i₁ ≫ l i) := by
    rw [Functor.map_comp, Spec.map_comp]
    rfl
  exact ⟨v, by rwa [hmap]⟩

/-- **The first step of the proof of Stacks 0E0D: splitting an integral morphism over an étale
neighbourhood.** Let `f' : X ⟶ Y'` be surjective on points and `π : Y' ⟶ Y` integral, with
`f' ≫ π` quasi-compact and locally of finite type.  Then every point `y` of `Y` is the image of a
point `z₀` of an affine étale chart `ξ₀ : U₀ ⟶ Y` such that the base change of `π` to `U₀` is an
integral morphism of affine schemes `p₀ : T₀ ⟶ U₀`, and `T₀` is covered by finitely many affine
pieces `V i`, open and closed in `T₀`, each of which has exactly one point `v` over `z₀`, with
`κ(v)` purely inseparable over `κ(z₀)`.

The proof follows Stacks 0E0D: by Stacks 0E1C the base change of `π` to an affine étale chart
through `y` has finite fibres with finite residue field extensions, and Stacks 0BSR splits it
after a further étale base change. -/
theorem exists_split_affine_chart
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (f' : X ⟶ Y') (π : Y' ⟶ Y) (hπint : IsIntegralHom B S hS π)
    (hqc : IsQuasiCompact B S hS (f' ≫ π)) (hlft : IsLocallyOfFiniteType B S hS (f' ≫ π))
    (hsurj : IsSurjective B S hS f') (y : points B S hS Y) :
    ∃ (U₀ T₀ : BigFppfOver B S hS) (ξ₀ : yoneda.obj U₀ ⟶ Y) (p₀ : T₀ ⟶ U₀)
      (e₀ : yoneda.obj T₀ ⟶ Y') (z₀ : points B S hS (yoneda.obj U₀)) (n : ℕ)
      (V : Fin n → BigFppfOver B S hS) (ι : ∀ i, V i ⟶ T₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ξ₀ ∧
      IsPullback e₀ (yoneda.map p₀) π ξ₀ ∧
      _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p₀) ∧
      pointsMap B S hS (yoneda.obj U₀) ξ₀ z₀ = y ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj T₀,
        ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
      ∀ i, ∃ v : (BigFppfOver.toScheme B S hS).obj (V i),
        ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀)) ⁻¹' {pointsToScheme B S hS U₀ z₀} = {v} ∧
        ((BigFppfOver.toScheme B S hS).map (ι i ≫ p₀)
          |>.residueFieldMap v).hom.IsPurelyInseparable := by
  -- An affine étale chart `W` through `y`, and the integral base change `T' ⟶ W` of `π`.
  obtain ⟨W, b, hWaff, hbet, w, hw⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  obtain ⟨T', p, e, hpb, hT'aff, hpint⟩ := hπint W hWaff b
  -- The base change of `f' ≫ π` to `W` factors through `T'` surjectively.
  have hsq₁ := IsPullback.of_hasPullback f' e
  have hbig := hsq₁.paste_vert hpb
  have hqcW : IsQuasiCompact B S hS (pullback.snd f' e ≫ yoneda.map p) :=
    isQuasiCompact_of_isPullback B S hS hbig hqc
  have hlftW : IsLocallyOfFiniteType B S hS (pullback.snd f' e ≫ yoneda.map p) :=
    isLocallyOfFiniteType_of_isPullback B S hS hbig.flip hbet hlft
  have hsurjW : IsSurjective B S hS (pullback.snd f' e) :=
    surjective_pointsMap_of_isPullback B S hS hsq₁ hsurj
  obtain ⟨U, g, hUcpt, hgsurj, hglft⟩ :=
    exists_compact_chart_over_affine B S hS (pullback.snd f' e) p hWaff hsurjW hqcW hlftW
  -- Stacks 0E1C: `T' ⟶ W` has finite fibres and finite residue field extensions, read on the
  -- spectra of the rings of global sections.
  have := hWaff
  have := hT'aff
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hUcpt
  have := hpint
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g ≫
      (BigFppfOver.toScheme B S hS).map p) := hglft
  obtain ⟨hfin, hres⟩ := finite_specMap_appTop_of_surjective_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map p) hgsurj
  obtain ⟨U₀, T₀, a₀, p₀, q₀, z₀, n, V, ι, hU₀, hT₀, ha₀, hsite, hp₀, hz₀, hV⟩ :=
    exists_split_affine_chart_of_isAffine B S hS p w hfin hres
  have hetale := isMultiplicative_presheaf_etale B S hS
  refine ⟨U₀, T₀, yoneda.map a₀ ≫ b, p₀, yoneda.map q₀ ≫ e, z₀, n, V, ι, hU₀, hT₀,
    MorphismProperty.comp_mem _ _ _ ha₀ hbet, (hsite.map yoneda).paste_horiz hpb, hp₀, ?_, hV⟩
  rw [pointsMap_comp_apply, hz₀, hw]

end AlgebraicGeometry.Space.ProperFlatStein

end

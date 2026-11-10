module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAtlasCompatible
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigSmoothChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# The chart data of Stacks 0GDH

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of algebraic
spaces over `S` and let `T ⊆ |X|` be closed, with `U ⊂ X` the open complement of `T` and
`U' = f⁻¹U`; this is the situation of Stacks 0GDB. Assume that `X` is locally Noetherian, `f` is
locally of finite type and `U' → U` is smooth, the hypotheses of **Stacks 0GDH**.

For a commuting square of étale charts `Spec A' ⟶ X'`, `Spec A ⟶ X` over `f`, whose horizontal
map is the spectrum of a ring map `φ : A → A'`, this file derives the remaining affine datum of the
source's proof: `Spec A' → Spec A` is smooth over the complement of the inverse image of `T`. The
source says: "Observe that `W'_{ij} → W_i` is locally of finite type and induces a smooth
morphism `W'_{ij} ∖ T'_{ij} → W_i ∖ T_i` (as this is true for `f` and these properties of
morphisms are étale local on the source and target)." The other two data, Noetherianity of `A`
and finite type of `φ`, do not depend on the property and are
`AlgebraicGeometry.FormalSpace.isNoetherianRing_of_isLocallyNoetherian_chart` and
`AlgebraicGeometry.FormalSpace.finiteType_of_isLocallyOfFiniteType_chart`.

Together with the affine case `isRigSmoothArrow_adicCompletionMap_of_smoothAwayFrom` this gives
the hypothesis `hP` of `correspondsToNoetherianMapAfterSourceCover_completionSheafMap` for
rig-smoothness: condition (4) of **Stacks 0GCQ** for `f_{/T}`, from which the implication
(4) ⟹ (1) of Stacks 0GCQ gives **Stacks 0GDH**.

## Main results

* `mem_smoothLocus_of_isSmooth_openComplementRestriction`: a chart square of a morphism smooth
  over the open complement of `T` is smooth off `T`.
* `smoothAwayFrom_of_isSmooth_openComplementRestriction_chart`: the affine datum.
* `correspondsToNoetherianMapAfterSourceCover_isRigSmoothArrow_completionSheafMap`: condition (4)
  of Stacks 0GCQ for `f_{/T}`, from compatible étale atlases of `X` and `X'`.
* `isRigSmooth_completionSheafMap_of_atlases`: `f_{/T}` is rig-smooth, from compatible étale
  atlases of `X` and `X'`.
* `isRigSmooth_completionSheafMap_of_isLocallyNoetherian`: **Stacks 0GDH**.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **A chart square of a morphism smooth over the open complement of `T` is smooth off `T`.**
Let `f : R ⟶ U` be a morphism of algebraic spaces over `S` and `T ⊆ |U|` closed, such that the
restriction `f⁻¹(|U| ∖ T) ⟶ |U| ∖ T` is smooth. For a commuting square of an étale chart
`pr : P ⟶ R`, an étale chart `ψ : V ⟶ U` and a morphism `α : P ⟶ V` of the site, every point of
`P` lying over the complement of `T` is in the smooth locus of the morphism of schemes underlying
`α`.

The point lies in an open subscheme `VP` of `P` whose morphism to `R` factors étalely through the
open subspace `U'` (`exists_opens_lift_openSubspaceOfPoints`); the composite `VP → U' → U ⊂ X` is
then smooth, and `VP → V` is the morphism of schemes it induces on the chart `ψ`. -/
theorem mem_smoothLocus_of_isSmooth_openComplementRestriction
    {R U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    (hU : IsAlgebraicSpace B S hS U) (f : R ⟶ U) (T : Set (Space.points B S hS U))
    (hT : IsClosed T)
    (haway : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    {P V : BigFppfOver B S hS} (pr : yoneda.obj P ⟶ R) (hpr : Space.IsEtale B S hS pr)
    (ψ : yoneda.obj V ⟶ U)
    (hψe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (α : P ⟶ V) (hcomm : yoneda.map α ≫ ψ = pr ≫ f)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α)]
    (p : Space.points B S hS (yoneda.obj P))
    (hp : Space.pointsMap B S hS (yoneda.obj P) (pr ≫ f) p ∉ T) :
    Space.pointsToScheme B S hS P p ∈ ((BigFppfOver.toScheme B S hS).map α).smoothLocus := by
  have hTcopen : IsOpen (Space.pointsMap B S hS R f ⁻¹' Tᶜ) :=
    hT.isOpen_compl.preimage (Space.continuous_pointsMap B S hS f)
  have hp' : Space.pointsMap B S hS (yoneda.obj P) pr p ∈ Space.pointsMap B S hS R f ⁻¹' Tᶜ := by
    change Space.pointsMap B S hS R f (Space.pointsMap B S hS (yoneda.obj P) pr p) ∈ Tᶜ
    rwa [← Space.pointsMap_comp_apply]
  obtain ⟨VP, -, hxVP, δ, hδe, hδ⟩ :=
    exists_opens_lift_openSubspaceOfPoints B S hS hR hTcopen pr hpr p hp'
  have hR'open := Space.isOpenSubspace_openSubspaceOfPoints B S hS hR _ hTcopen
  have hU'open := Space.isOpenSubspace_openSubspaceOfPoints_compl_of_isClosed B S hS hU T hT
  -- the chart of `U` attached to `VP` is smooth
  have hsm : Space.IsSmooth B S hS
      (yoneda.map (Space.openSiteObjectHom B S hS P VP) ≫ pr ≫ f) := by
    have h1 : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T ≫
        (Space.openSubspaceOfPoints B S hS U Tᶜ).ι) :=
      Space.isSmooth_comp B S hS hR'open.1 hU'open.1 hU _ _ haway
        (Space.isSmooth_of_isEtale B S hS hU (Space.isEtale_ι_of_isOpenSubspace hU'open))
    have h2 := Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hR'open.1 hU δ _
      (Space.isSmooth_of_isEtale B S hS hR'open.1 hδe) h1
    rwa [Space.openComplementRestriction_ι, ← Category.assoc, hδ, Category.assoc] at h2
  have hsm' : Smooth ((BigFppfOver.toScheme B S hS).map
      (Space.openSiteObjectHom B S hS P VP ≫ α)) :=
    hsm _ _ (𝟙 _) ψ _ (Space.presheaf_etale_id B S hS _) hψe
      (by rw [Functor.map_comp, Category.assoc, hcomm, Category.id_comp])
  have hsm'' : Smooth (VP.ι ≫ (BigFppfOver.toScheme B S hS).map α) := by
    rwa [Functor.map_comp, Space.map_openSiteObjectHom] at hsm'
  have hstalk : ((VP.ι ≫ (BigFppfOver.toScheme B S hS).map α).stalkMap
      (⟨_, hxVP⟩ : VP.toScheme)).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp
      (by rw [@Scheme.Hom.smoothLocus_eq_top _ _ _ hsm'']; trivial)
  have hmem : (⟨_, hxVP⟩ : VP.toScheme) ∈
      VP.ι ⁻¹ᵁ ((BigFppfOver.toScheme B S hS).map α).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact hstalk
  exact hmem

/-- **The smooth locus of the spectrum of a ring map, read on primes.** For a ring map
`φ : A → A'` of finite presentation, a prime `q` of `A'` at which the stalk map of
`Spec A' → Spec A` is formally smooth, that is a point of its smooth locus, is a prime at which
`A → A'` is smooth in the sense of Definition 00TB. -/
theorem smoothAt_of_formallySmooth_stalkMap_Spec_map {A A' : Type u} [CommRing A]
    [CommRing A'] (φ : A →+* A') (hφ : φ.FinitePresentation) (q : PrimeSpectrum A')
    (hq : ((Spec.map (CommRingCat.ofHom φ)).stalkMap q).hom.FormallySmooth) :
    letI : Algebra A A' := φ.toAlgebra
    Algebra.SmoothAt A A' q.asIdeal := by
  let : Algebra A A' := φ.toAlgebra
  have : Algebra.FinitePresentation A A' := hφ
  rw [Algebra.smoothAt_iff_isSmoothAt]
  have h1 := (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom φ) q)).mp hq
  let p : Ideal A := q.asIdeal.comap (algebraMap A A')
  have : q.asIdeal.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have h2 : Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    RingHom.formallySmooth_algebraMap.mp h1
  exact Algebra.FormallySmooth.iff_restrictScalars.mpr h2

/-- **The chart map is smooth off the inverse image of `T`.** For a chart square over a morphism
`f` whose restriction to the open complement of a closed `T` is smooth, with `A` Noetherian and a
finite type ring map `φ : A → A'`, and an ideal `J ⊆ A` cutting out the inverse image of `T` in
`Spec A`, the map `Spec A' → Spec A` is smooth over `Spec A ∖ V(J)`. -/
theorem smoothAwayFrom_of_isSmooth_openComplementRestriction_chart
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    {A A' : Type u} [CommRing A] [CommRing A'] [IsNoetherianRing A]
    (hA : B.Contains (Spec (.of A)))
    (hA' : B.Contains (Spec (.of A'))) (str : Spec (.of A) ⟶ S) (φ : A →+* A')
    (hφ : φ.FiniteType)
    (a : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (a' : yoneda.obj (affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str)) ⟶ X')
    (ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a')
    (h : affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str) ⟶
      affineOver B S hS hA str)
    (hh : h = Space.specSiteObjectMap φ hA hA' str)
    (hsq : yoneda.map h ≫ a = a' ≫ f) (J : Ideal A)
    (hJ : Space.pointsMap B S hS _ a ⁻¹' T = zeroLocusPoints B S hS hA str J) :
    letI : Algebra A A' := φ.toAlgebra
    Rig.SmoothAwayFrom A J A' := by
  let : Algebra A A' := φ.toAlgebra
  have hfp : φ.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp hφ
  have hF : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hfp
  have hhF : (BigFppfOver.toScheme B S hS).map h = Spec.map (CommRingCat.ofHom φ) := by
    rw [hh]
    rfl
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) := by
    rwa [hhF]
  intro q hq hqJ
  obtain ⟨p, hpx⟩ := Space.surjective_pointsToScheme B S hS
    (affineOver B S hS hA' (Spec.map (CommRingCat.ofHom φ) ≫ str)) (⟨q, hq⟩ : PrimeSpectrum A')
  have hmem := mem_smoothLocus_of_isSmooth_openComplementRestriction hX' hX f T hT hsm a'
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS a').mpr ha') a ha h hsq p ?_
  · rw [Scheme.Hom.mem_smoothLocus, hpx, hhF] at hmem
    exact smoothAt_of_formallySmooth_stalkMap_Spec_map φ hfp ⟨q, hq⟩ hmem
  · intro hpT
    apply hqJ
    have hp1 : Space.pointsMap B S hS _ (yoneda.map h) p ∈ zeroLocusPoints B S hS hA str J := by
      rwa [← hJ, Set.mem_preimage, ← Space.pointsMap_comp_apply, hsq]
    have hp2 := (zeroLocusPoints_eq_preimage_pointsToScheme B S hS hA str J).subset hp1
    have hp3 : Spec.map (CommRingCat.ofHom φ) (⟨q, hq⟩ : PrimeSpectrum A') ∈
        PrimeSpectrum.zeroLocus (J : Set A) := by
      have e := Space.pointsToScheme_pointsMap B S hS h p
      rw [hhF, hpx] at e
      exact e ▸ hp2
    exact Ideal.map_le_iff_le_comap.mpr ((PrimeSpectrum.mem_zeroLocus _ _).mp hp3)

/-- **Condition (4) of Stacks 0GCQ for `f_{/T}`.** In the situation of Stacks 0GDB, with `X`
locally Noetherian, `f` locally of finite type and `U' → U` smooth — the hypotheses of Stacks
0GDH — let `{Spec A_i ⟶ X}` be an étale covering of `X` and `{Spec A'_k ⟶ X'}` one of `X'`, each
`Spec A'_k` mapping to `Spec A_{ι k}` by the spectrum of a ring map `φ k` compatibly with `f`.
Then the completed charts `(Spec A'_k)_{/T'} ⟶ X'_{/T'}` form a covering as in Definition 0AIM
whose members factor through the completed charts of `X_{/T}` by maps corresponding to
rig-smooth maps in `WAdm^{Noeth}`.

This is the source's reduction of Stacks 0GDH to the affine case together with the affine case
itself (part (1) of Stacks 0GAK). -/
theorem correspondsToNoetherianMapAfterSourceCover_isRigSmoothArrow_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T) (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    {Ik : Type (u + 1)} {A' : Ik → Type u} [∀ k, CommRing (A' k)]
    (ι : Ik → Ix) (φ : ∀ k, A (ι k) →+* A' k)
    (hA' : ∀ k, B.Contains (AlgebraicGeometry.Spec (.of (A' k))))
    (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X')
    (ha' : ∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a' k))
    (hcov' : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun k ↦ Space.sheafifiedULiftMap B S hS (a' k)))
    (h : ∀ k, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k)) ⟶
      affineOver B S hS (hA (ι k)) (str (ι k)))
    (hh : ∀ k, h k = Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k)))
    (hsq : ∀ k, yoneda.map (h k) ≫ a (ι k) = a' k ≫ f) :
    CorrespondsToNoetherianMapAfterSourceCover B S hS (fun φ ↦ RingHom.IsRigSmoothArrow φ)
      (Space.completionSheafMap B S hS f T) := by
  have hAN : ∀ i, IsNoetherianRing (A i) := fun i ↦
    isNoetherianRing_of_isLocallyNoetherian_chart hXN (hA i) (str i) (a i) (ha i)
  have hft : ∀ k, (φ k).FiniteType := fun k ↦
    finiteType_of_isLocallyOfFiniteType_chart f hf (hA (ι k)) (hA' k) (str (ι k)) (φ k)
      (a (ι k)) (ha (ι k)) (a' k) (ha' k) (h k) (hh k) (hsq k)
  have hA'N : ∀ k, IsNoetherianRing (A' k) := fun k ↦
    let : Algebra (A (ι k)) (A' k) := (φ k).toAlgebra
    have : Algebra.FiniteType (A (ι k)) (A' k) := hft k
    Algebra.FiniteType.isNoetherianRing (A (ι k)) (A' k)
  have hsh : ∀ {W : BigFppfOver B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hZ : IsAlgebraicSpace B S hS Z) (b : yoneda.obj W ⟶ Z),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS b).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS b).hom hai := fun hZ b hb ↦
    exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS _) hZ b
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS b).mpr hb)
  exact correspondsToNoetherianMapAfterSourceCover_completionSheafMap
    (fun φ ↦ RingHom.IsRigSmoothArrow φ)
    propertyInvariantUnderRingEquiv_isRigSmoothArrow hX' hX f T hT hA str a
    (fun i ↦ hsh hX (a i) (ha i)) hcov ι φ hA' a' (fun k ↦ hsh hX' (a' k) (ha' k)) hcov' h hh
    hsq fun k J hJ ↦ isRigSmoothArrow_adicCompletionMap_of_smoothAwayFrom (φ k) J (hft k)
      (smoothAwayFrom_of_isSmooth_openComplementRestriction_chart hX' hX f T hT hsm
        (hA (ι k)) (hA' k) (str (ι k)) (φ k) (hft k) (a (ι k)) (ha (ι k)) (a' k) (ha' k) (h k)
        (hh k) (hsq k) J hJ)

/-- **Stacks 0GDH, assembled from the cover.** In the situation of Stacks 0GDB, if `X` is locally
Noetherian, `f` is locally of finite type and `U' → U` is smooth, then `f_{/T}` is rig-smooth,
given compatible étale atlases of `X` and `X'` read in the value universe of the formal algebraic
spaces.

This is condition (4) of Stacks 0GCQ for `f_{/T}`,
`correspondsToNoetherianMapAfterSourceCover_isRigSmoothArrow_completionSheafMap`, followed by the
implication (4) ⟹ (1) of Stacks 0GCQ,
`isRigSmooth_of_correspondsToNoetherianMapAfterSourceCover`. The atlases are produced by
`AlgebraicGeometry.FormalSpace.exists_compatible_affineOver_atlases`. -/
theorem isRigSmooth_completionSheafMap_of_atlases
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : IsClosed T) (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    {Ik : Type (u + 1)} {A' : Ik → Type u} [∀ k, CommRing (A' k)]
    (ι : Ik → Ix) (φ : ∀ k, A (ι k) →+* A' k)
    (hA' : ∀ k, B.Contains (AlgebraicGeometry.Spec (.of (A' k))))
    (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X')
    (ha' : ∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a' k))
    (hcov' : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun k ↦ Space.sheafifiedULiftMap B S hS (a' k)))
    (h : ∀ k, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k)) ⟶
      affineOver B S hS (hA (ι k)) (str (ι k)))
    (hh : ∀ k, h k = Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k)))
    (hsq : ∀ k, yoneda.map (h k) ≫ a (ι k) = a' k ≫ f) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) :=
  isRigSmooth_of_correspondsToNoetherianMapAfterSourceCover B S hS _
    (correspondsToNoetherianMapAfterSourceCover_isRigSmoothArrow_completionSheafMap hX' hX f T hT
      hXN hf hsm hA str a ha hcov ι φ hA' a' ha' hcov' h hh hsq)

/-- **Stacks 0GDH.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`, let
`T ⊆ |X|` be closed, and let `U ⊆ X` be the open complement of `T` and `U' = f⁻¹U` (the
situation of Stacks 0GDB). If `X` is locally Noetherian, `f` is locally of finite type and
`U' → U` is smooth, then the completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-smooth.

The proof is the source's: compatible étale atlases of `X` and `X'` by spectra of rings
(Properties of Spaces, Lemma 03FX; `exists_compatible_affineOver_atlases`), condition (4) of
Stacks 0GCQ for `f_{/T}` from them
(`correspondsToNoetherianMapAfterSourceCover_isRigSmoothArrow_completionSheafMap`: the reduction
to the affine case and the affine case by Stacks 0GAK and Stacks 0GAM), and the implication
(4) ⟹ (1) of Stacks 0GCQ. -/
@[stacks 0GDH]
theorem isRigSmooth_completionSheafMap_of_isLocallyNoetherian
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T)) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) := by
  obtain ⟨Ix, A, instA, hA, str, a, ha, hcov, Ik, A', instA', ι, φ, hA', a', ha', hcov', hsq⟩ :=
    exists_compatible_affineOver_atlases hX' hX f
  let := instA
  let := instA'
  exact isRigSmooth_completionSheafMap_of_atlases hX' hX f T hT hXN hf hsm
    (A := fun i : ULift.{u + 1} Ix ↦ A i.down) (fun i ↦ hA i.down) (fun i ↦ str i.down)
    (fun i ↦ a i.down) (fun i ↦ ha i.down)
    (isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover hX.isSheaf a hcov)
    (A' := fun k : ULift.{u + 1} Ik ↦ A' k.down) (fun k ↦ ULift.up (ι k.down))
    (fun k ↦ φ k.down) (fun k ↦ hA' k.down) (fun k ↦ a' k.down) (fun k ↦ ha' k.down)
    (isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover hX'.isSheaf a' hcov')
    (fun k ↦ Space.specSiteObjectMap (φ k.down) (hA (ι k.down)) (hA' k.down) (str (ι k.down)))
    (fun _ ↦ rfl) (fun k ↦ hsq k.down)

end AlgebraicGeometry.FormalSpace

end

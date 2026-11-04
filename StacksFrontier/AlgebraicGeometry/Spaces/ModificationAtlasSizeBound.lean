module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveFiniteTypeCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The size of an atlas of a modification, bounded by its points

Let `p : Z ⟶ h_R` be a morphism locally of finite type from an algebraic space to the
representable presheaf of an object `R` of the big fppf site. This file bounds the size of an
étale atlas of `Z` by the number of points of `Z` and the size of `R`, and then bounds the
number of points of `Z` in the situation of Stacks 0ARB: `Z` is an isomorphism over the open
complement `U` of a set `T` of points of `R`, and the points of `Z` over `T` are covered by a
representable presheaf `h_P`, in the sense that `h_P` maps locally surjectively onto the
subfunctor of `Z` cut out by the points over `T`.

This is the size bound that effective descent along a covering of arbitrary size needs
(`AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_size_le`). Effectivity fails in
general for an étale covering by affines whose descended pieces are only locally of finite
type, so in Stacks 0ARB the bound has to come from the formal side: the completion of `Z`
along the inverse image of `T` is a formal algebraic space, which satisfies the set-theoretic
condition of Stacks 0AIS and so is covered by a representable.

## Main results

* `AlgebraicGeometry.Space.exists_atlas_size_le_of_injective_points`: if the points of `Z` inject
  into a type of cardinality at most `μ`, and `size R ≤ μ < cutoff`, then `Z` has a surjective
  étale atlas of size at most `μ`.
* `AlgebraicGeometry.Space.injOn_pointsMap_of_isIso_pullback_snd`: a morphism which is an
  isomorphism over the subspace cut out by `Tᶜ` is injective on the points over `Tᶜ`.
* `AlgebraicGeometry.Space.subset_range_pointsMap_of_isLocallySurjective`: a locally surjective
  map onto the subspace cut out by a set of points hits every point of that set.
* `AlgebraicGeometry.Space.exists_atlas_size_le_of_isIso_pullback_snd`: the combination, the
  uniform atlas bound for a modification of `R` outside `T` whose points over `T` are covered
  by `h_P`, in terms of `size R`, `#R` and `#P` only.

## References

* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space locally of finite type over an object of the site has an atlas no
larger than its set of points allows.**

Let `p : Z ⟶ h_R` be locally of finite type, `Z` an algebraic space, and let the points of `Z`
inject into a type `K` with `#K ≤ μ`, where `ℵ₀ ≤ μ < B.cutoff` and `size R ≤ μ`. Then `Z` has
a surjective étale atlas `h_V ⟶ Z` with `size V ≤ μ`.

Choose any atlas `h_U ⟶ Z`. For each point of `Z` choose a point of `U` over it and an affine
open of `U` containing that point. Each such affine open is quasi-compact and locally of finite
type over `R`, so Stacks 04T7 bounds its size by `size R`. The disjoint union of these affine
opens lies in the site, has size at most `μ`, and is étale and surjective over `Z`. -/
theorem exists_atlas_size_le_of_injective_points {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {R : BigFppfOver B S hS} (p : Z ⟶ yoneda.obj R)
    (hp : IsLocallyOfFiniteType B S hS p) {K : Type u} (e : points B S hS Z → K)
    (he : Function.Injective e) {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff)
    (hK : #K ≤ μ) (hR : ((BigFppfOver.toScheme B S hS).obj R).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  classical
  let A := BigFppfOver.toScheme B S hS
  obtain ⟨U, q, hqs, hqe⟩ := hZ.exists_atlas
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hR' := isAlgebraicSpace_yoneda B S hS R
  -- the atlas is locally of finite type over `R`
  have hcomp : IsLocallyOfFiniteType B S hS (q ≫ p) :=
    isLocallyOfFiniteType_comp B S hS hU hZ hR' q p
      (holdsOnEveryEtaleChart_of_isEtale B S hS
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (fun _ hg => have := hg; inferInstance) hZ
        ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hqe))
      hp
  have hgmap : IsLocallyOfFiniteType B S hS (yoneda.map (yoneda.preimage (q ≫ p))) := by
    rwa [Functor.map_preimage]
  have _ : LocallyOfFiniteType (A.map (yoneda.preimage (q ≫ p))) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (yoneda.preimage (q ≫ p))).1 hgmap
  -- every point of `Z` comes from a point of the atlas
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) q) :=
    (surjective_iff_surjective_pointsMap B S hS Z hZ U q).1 hqs
  let K' := Set.range e
  have hK' : #K' ≤ μ := (mk_le_of_injective Subtype.val_injective).trans hK
  choose z hz using fun k : K' => k.2
  have hsurj' : ∀ y, ∃ x : A.obj U,
      pointsMap B S hS (yoneda.obj U) q ((pointsEquivScheme B S hS U).symm x) = y :=
    hsurj.comp (pointsEquivScheme B S hS U).symm.surjective
  choose x hx using fun k : K' => hsurj' (z k)
  have hO : ∀ k : K', ∃ O : (A.obj U).Opens, IsAffineOpen O ∧ x k ∈ O := fun k =>
    let ⟨O, hO, hxO, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (A.obj U).isBasis_affineOpens (TopologicalSpace.Opens.mem_top (x k))
    ⟨O, hO, hxO⟩
  choose O hOaff hxO using hO
  have hsizeO : ∀ k, (O k).toScheme.size ≤ μ := by
    intro k
    have : IsAffine (O k).toScheme := hOaff k
    exact (Scheme.size_le_of_locallyOfFiniteType
      ((O k).ι ≫ A.map (yoneda.preimage (q ≫ p)))).trans hR
  -- the affine opens, as objects of the site, and their disjoint union
  let Y : K' → BigFppfOver B S hS := fun k =>
    Over.mk (Y := B.obj ((Scheme.size_coe_opens_le _ (O k)).trans_lt U.left.property))
      (X := B.obj hS) ⟨(O k).ι ≫ U.hom.hom⟩
  let o : ∀ k, Y k ⟶ U := fun k => Over.homMk ⟨(O k).ι⟩
  obtain ⟨V, j, -, -, ⟨hVs⟩, ⟨hV⟩, -⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS Y hμ hK' hsizeO
  let d : V ⟶ U := hV.desc (Cofan.mk U o)
  have hd : ∀ k, j k ≫ d = o k := fun k => hV.fac (Cofan.mk U o) ⟨k⟩
  have hdA : ∀ k, A.map (j k) ≫ A.map d = (O k).ι := fun k => by
    rw [← A.map_comp, hd]
    rfl
  -- the underlying scheme of `V` is the coproduct of the affine opens
  let eV : A.obj V ≅ ∐ fun k : K' => ((O k).toScheme : Scheme.{u}) :=
    hVs.coconePointUniqueUpToIso
      (colimit.isColimit (Discrete.functor fun k : K' => ((O k).toScheme : Scheme.{u})))
  have hdeq : A.map d = eV.hom ≫ Sigma.desc fun k : K' => (O k).ι := by
    refine hVs.hom_ext fun k => ?_
    rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    simp only [Cofan.mk_ι_app, colimit.cocone_ι, Discrete.functor_obj_eq_as]
    rw [hdA k.as]
    exact (Sigma.ι_desc (fun k : K' => (O k).ι) k.as).symm
  have hdet : Etale (A.map d) := by
    let : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
    have : Etale (Sigma.desc fun k : K' => (O k).ι) :=
      IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun k => by infer_instance)
    rw [hdeq]
    infer_instance
  have hsizeV : (A.obj V).size ≤ μ := by
    rw [Scheme.size_congr eV]
    exact schemeSize_coproduct_le _ μ hℵ hK' hsizeO
  -- the induced map on points, through the representing schemes
  have hpts : ∀ v : A.obj V, pointsMap B S hS (yoneda.obj V) (yoneda.map d)
      ((pointsEquivScheme B S hS V).symm v) = (pointsEquivScheme B S hS U).symm (A.map d v) := by
    intro v
    apply (pointsEquivScheme B S hS U).injective
    rw [Equiv.apply_symm_apply]
    show pointsToScheme B S hS U _ = _
    rw [pointsToScheme_pointsMap_yoneda]
    exact congrArg (A.map d) ((pointsEquivScheme B S hS V).apply_symm_apply v)
  refine ⟨V, yoneda.map d ≫ q, ?_, etale_comp_of_scheme B S hS d q hdet hqe, hsizeV⟩
  refine (surjective_iff_surjective_pointsMap B S hS Z hZ V (yoneda.map d ≫ q)).2 fun w => ?_
  let k : K' := ⟨e w, w, rfl⟩
  have hzk : z k = w := he (hz k)
  let y : (O k).toScheme := ⟨x k, hxO k⟩
  refine ⟨(pointsEquivScheme B S hS V).symm (A.map (j k) y), ?_⟩
  rw [pointsMap_comp_apply, hpts, ← hzk, ← hx k]
  congr 2
  rw [← Scheme.Hom.comp_apply, hdA k]
  rfl

/-- **A modification is injective on the points over the open part.** If the base change of
`p : Z ⟶ X` to the subspace of `X` cut out by `Tᶜ` is an isomorphism, then `p` is injective on
the points of `Z` lying over `Tᶜ`.

Those points are the points of the subspace of `Z` cut out by their set (Stacks 03BZ), which
`p` maps isomorphically onto the subspace of `X` cut out by `Tᶜ`, and the points of a
subfunctor inject into the points of the ambient presheaf. -/
theorem injOn_pointsMap_of_isIso_pullback_snd {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Z ⟶ X) (T : Set (points B S hS X))
    (h : IsIso (pullback.snd p (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    Set.InjOn (pointsMap B S hS Z p) (pointsMap B S hS Z p ⁻¹' Tᶜ) := by
  have hr := isIso_openComplementRestriction B S hS p T h
  set G := openSubspaceOfPoints B S hS Z (pointsMap B S hS Z p ⁻¹' Tᶜ)
  set r := openComplementRestriction B S hS p T
  have hsq : G.ι ≫ p = r ≫ (openSubspaceOfPoints B S hS X Tᶜ).ι :=
    (openComplementRestriction_ι B S hS p T).symm
  have hrange : Set.range (pointsMap B S hS G.toFunctor G.ι) = pointsMap B S hS Z p ⁻¹' Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  intro z₁ hz₁ z₂ hz₂ heq
  rw [← hrange] at hz₁ hz₂
  obtain ⟨w₁, rfl⟩ := hz₁
  obtain ⟨w₂, rfl⟩ := hz₂
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq, pointsMap_comp_apply,
    pointsMap_comp_apply] at heq
  have h₂ := congrArg (pointsMap B S hS _ (inv r))
    (pointsMap_injective_of_mono B S hS (openSubspaceOfPoints B S hS X Tᶜ).ι heq)
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, IsIso.hom_inv_id, pointsMap_id_apply,
    pointsMap_id_apply] at h₂
  rw [h₂]

/-- **A locally surjective cover of the subspace cut out by a set of points hits every point of
that set.** If `c : P ⟶ Z_T` is locally surjective onto the subfunctor `Z_T` of `Z` cut out by a
set `T'` of points of `Z`, then every point of `T'` is the image of a point of `P`. -/
theorem subset_range_pointsMap_of_isLocallySurjective {Z P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T' : Set (points B S hS Z)) (c : P ⟶ (openSubspaceOfPoints B S hS Z T').toFunctor)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c) :
    T' ⊆ Set.range (pointsMap B S hS P (c ≫ (openSubspaceOfPoints B S hS Z T').ι)) := by
  intro z hz
  rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS T'] at hz
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := surjective_pointsMap_of_isLocallySurjective B S hS c hc w
  exact ⟨v, pointsMap_comp_apply B S hS c _ v⟩

/-- **The uniform atlas bound for a modification whose points over `T` are covered by a
representable.**

Let `R` be an object of the site, `T` a set of points of `h_R` with complement cut out by the
subspace `U`, and `p : Z ⟶ h_R` a morphism locally of finite type from an algebraic space which
is an isomorphism over `U`. Suppose that an object `P` of the site maps locally surjectively onto
the subspace of `Z` cut out by the points over `T`. Then for any cardinal `μ` with
`ℵ₀ ≤ μ < B.cutoff` bounding `size R`, the cardinality of `R` and the cardinality of `P`, the
space `Z` has a surjective étale atlas of size at most `μ`.

The bound depends on `Z` only through `P`. In Stacks 0ARB, `Z` is a member of the descent datum
built from the affine case, and `P` comes from the set-theoretic condition (Stacks 0AIS) on the
completion of `Z` along the inverse image of `T`, which is the formal algebraic space `W` given
in the source, base changed to `R`. -/
theorem exists_atlas_size_le_of_isIso_pullback_snd {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {R : BigFppfOver B S hS} (p : Z ⟶ yoneda.obj R)
    (hp : IsLocallyOfFiniteType B S hS p) (T : Set (points B S hS (yoneda.obj R)))
    (hiso : IsIso (pullback.snd p (openSubspaceOfPoints B S hS (yoneda.obj R) Tᶜ).ι))
    {P : BigFppfOver B S hS}
    (c : yoneda.obj P ⟶
      (openSubspaceOfPoints B S hS Z (pointsMap B S hS Z p ⁻¹' T)).toFunctor)
    (hc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff)
    (hR : ((BigFppfOver.toScheme B S hS).obj R).size ≤ μ)
    (hRpts : #((BigFppfOver.toScheme B S hS).obj R) ≤ μ)
    (hPpts : #((BigFppfOver.toScheme B S hS).obj P) ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  classical
  let T' := pointsMap B S hS Z p ⁻¹' T
  have hcov := subset_range_pointsMap_of_isLocallySurjective _ c hc
  have hinj := injOn_pointsMap_of_isIso_pullback_snd p T hiso
  -- a point over `T` is sent to a chosen point of `P` above it, any other to its image in `R`
  let e : points B S hS Z →
      (BigFppfOver.toScheme B S hS).obj R ⊕ (BigFppfOver.toScheme B S hS).obj P := fun z =>
    if h : z ∈ T' then .inr (pointsEquivScheme B S hS P (hcov h).choose)
    else .inl (pointsEquivScheme B S hS R (pointsMap B S hS Z p z))
  have he : Function.Injective e := by
    intro z₁ z₂ h
    by_cases h₁ : z₁ ∈ T' <;> by_cases h₂ : z₂ ∈ T' <;>
      simp only [e, h₁, h₂, dite_true, dite_false, reduceCtorEq, Sum.inl.injEq,
        Sum.inr.injEq] at h
    · rw [← (hcov h₁).choose_spec, ← (hcov h₂).choose_spec,
        (pointsEquivScheme B S hS P).injective h]
    · exact hinj h₁ h₂ ((pointsEquivScheme B S hS R).injective h)
  have hK : #((BigFppfOver.toScheme B S hS).obj R ⊕ (BigFppfOver.toScheme B S hS).obj P) ≤ μ := by
    rw [mk_sum, lift_id, lift_id]
    exact (add_le_add hRpts hPpts).trans (add_eq_self hℵ).le
  exact exists_atlas_size_le_of_injective_points hZ p hp e he hℵ hμ hK hR

/-- **A surjection onto a completion from a representable sheaf is a locally surjective map onto
the subspace cut out by the points.** Let `Z` be an fppf sheaf and `T'` a set of its points. A
surjection `h_P ⟶ Z_{/T'}` of fppf sheaves in the value universe of the formal algebraic spaces,
from the universe-lifted sheaf represented by an object `P`, comes from a locally surjective map
`h_P ⟶ Z_{T'}` of presheaves of `Type u`, where `Z_{T'}` is the subfunctor of `Z` cut out by
`T'`.

For a sheaf `Z` the completion is that subfunctor, universe-lifted
(`AlgebraicGeometry.Space.completionSheafIsoSubfunctor` and
`AlgebraicGeometry.Space.completionSubfunctorIso`), and a morphism of universe lifts is the lift
of a unique morphism, with the same image sieves. -/
theorem exists_isLocallySurjective_of_epi_completionSheaf {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z) (T' : Set (points B S hS Z))
    (P : BigFppfOver B S hS)
    (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj P ⟶ completionSheaf B S hS Z T')
    [Epi q] :
    ∃ c : yoneda.obj P ⟶ (openSubspaceOfPoints B S hS Z T').toFunctor,
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c := by
  let J := BigFppfOver.topology B S hS
  have hq : Presheaf.IsLocallySurjective J q.hom := (Sheaf.isLocallySurjective_iff_epi q).2 ‹_›
  let eP : (J.uliftYoneda.{u + 1}.obj P).obj ≅ uliftYoneda.{u + 1}.obj P :=
    J.uliftYonedaCompSheafToPresheaf.app P
  let ψ : uliftYoneda.{u + 1}.obj P ⟶
      (openSubspaceOfPoints B S hS Z T').toFunctor ⋙ uliftFunctor.{u + 1} :=
    eP.inv ≫ q.hom ≫ (completionSheafIsoSubfunctor B S hS hZ T').hom ≫
      (completionSubfunctorIso B S hS Z T').hom
  have hψ : Presheaf.IsLocallySurjective J ψ := by
    dsimp only [ψ]
    infer_instance
  let c : yoneda.obj P ⟶ (openSubspaceOfPoints B S hS Z T').toFunctor :=
    (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight _).preimage ψ
  have hc : Functor.whiskerRight c uliftFunctor.{u + 1} = ψ :=
    (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight _).map_preimage ψ
  refine ⟨c, ⟨fun {U} s => J.superset_covering ?_ (hψ.imageSieve_mem (ULift.up.{u + 1} s))⟩⟩
  rintro V i ⟨t, ht⟩
  rw [← hc] at ht
  exact ⟨t.down, congrArg ULift.down ht⟩

/-- **The uniform atlas bound, with the cover on the formal side.** As
`AlgebraicGeometry.Space.exists_atlas_size_le_of_isIso_pullback_snd`, with the covering of the
points of `Z` over `T` given as a surjection of fppf sheaves `h_P ⟶ Z_{/T'}` onto the completion
of `Z` along `T' = |p|⁻¹T`. This is the form in which the set-theoretic condition of Stacks 0AIS
on a formal algebraic space provides it. -/
theorem exists_atlas_size_le_of_epi_completionSheaf {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {R : BigFppfOver B S hS} (p : Z ⟶ yoneda.obj R)
    (hp : IsLocallyOfFiniteType B S hS p) (T : Set (points B S hS (yoneda.obj R)))
    (hiso : IsIso (pullback.snd p (openSubspaceOfPoints B S hS (yoneda.obj R) Tᶜ).ι))
    {P : BigFppfOver B S hS}
    (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj P ⟶
      completionSheaf B S hS Z (pointsMap B S hS Z p ⁻¹' T)) [Epi q]
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff)
    (hR : ((BigFppfOver.toScheme B S hS).obj R).size ≤ μ)
    (hRpts : #((BigFppfOver.toScheme B S hS).obj R) ≤ μ)
    (hPpts : #((BigFppfOver.toScheme B S hS).obj P) ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Z),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj V).size ≤ μ := by
  obtain ⟨c, hc⟩ := exists_isLocallySurjective_of_epi_completionSheaf hZ.isSheaf _ P q
  exact exists_atlas_size_le_of_isIso_pullback_snd hZ p hp T hiso c hc hℵ hμ hR hRpts hPpts

end AlgebraicGeometry.Space

end

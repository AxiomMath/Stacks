module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Open immersions of algebraic spaces from an isomorphism over a dense open of the target

A separated, flat morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite type is an open immersion as soon as it is an isomorphism over a quasi-compact
scheme-theoretically dense open subspace of its target. This is the algebraic-space form of
Stacks 081M.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_of_isIso_pullback_snd`: a separated, flat morphism
  locally of finite type which is an isomorphism over a quasi-compact scheme-theoretically dense
  open subspace of its target is an open immersion.
* `AlgebraicGeometry.Space.dense_range_pointsMap_ι_of_isSchemeTheoreticallyDense`: a
  scheme-theoretically dense open subspace has topologically dense point set.

## References

* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
* [Stacks Project, Tag 0878](https://stacks.math.columbia.edu/tag/0878)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0836](https://stacks.math.columbia.edu/tag/0836)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site needs the larger budget
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_OpenImmersionFromDenseOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_OpenImmersionFromDenseOpen
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- Pullbacks in the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_bigFppfOver_OpenImmersionFromDenseOpen
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Topological density of the point set of the open subspace -/

/-- A scheme-theoretically dense open subscheme is topologically dense. -/
private theorem dense_of_isSchemeTheoreticallyDense {Z : Scheme.{u}} (W : Z.Opens)
    (hW : Scheme.Opens.IsSchemeTheoreticallyDense W) : Dense (W : Set Z) := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨x, hx⟩
  by_contra hdis
  let UO : Z.Opens := ⟨O, hO⟩
  have hbot : UO.ι ⁻¹ᵁ W = ⊥ :=
    le_antisymm (fun y hy => (hdis ⟨y.1, y.2, hy⟩).elim) bot_le
  have hdom := hW UO
  rw [hbot] at hdom
  have : QuasiCompact (⊥ : UO.toScheme.Opens).ι := ⟨fun _ _ _ => by
    convert isCompact_empty (X := (⊥ : UO.toScheme.Opens).toScheme) using 1
    exact Set.eq_empty_iff_forall_notMem.mpr fun z _ => z.2.elim⟩
  have : Nonempty UO.toScheme := ⟨⟨x, hx⟩⟩
  obtain ⟨z⟩ := (IsDominant.denseRange (f := (⊥ : UO.toScheme.Opens).ι)).nonempty
  exact z.2.elim

/-- A scheme-theoretically dense open subspace of an algebraic space has topologically dense
point set. -/
theorem dense_range_pointsMap_ι_of_isSchemeTheoreticallyDense
    (hY : IsAlgebraicSpace B S hS Y) (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVdense : IsSchemeTheoreticallyDense B S hS V) :
    Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  obtain ⟨U, b, hsurjb, hetaleb⟩ := hY.exists_atlas
  have hoi : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)) := hV.2.property_snd b
  have hWdense : Dense (Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b))) := by
    have hch := isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense B S hS V hV
      hVdense ⟨CostructuredArrow.mk b, hetaleb⟩
    rw [← opensRange_snd_eq_chartOpenOfOpenSubspace B S hS V hV
      ⟨CostructuredArrow.mk b, hetaleb⟩] at hch
    exact dense_of_isSchemeTheoreticallyDense _ hch
  set e := schemePointsHomeomorph B S hS U with he
  have hnat (w : points B S hS (yoneda.obj (hV.2.rep.pullback b))) :
      e (pointsMap B S hS (yoneda.obj (hV.2.rep.pullback b))
          (yoneda.map (hV.2.rep.snd b)) w) =
        (BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)
          (schemePointsHomeomorph B S hS (hV.2.rep.pullback b) w) := by
    rw [he, schemePointsHomeomorph_apply, schemePointsHomeomorph_apply]
    exact pointsToScheme_pointsMap B S hS (hV.2.rep.snd b) w
  have himage : e '' Set.range (pointsMap B S hS (yoneda.obj (hV.2.rep.pullback b))
      (yoneda.map (hV.2.rep.snd b))) =
      Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)) := by
    rw [← Set.range_comp]
    refine Set.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨w, rfl⟩
      exact ⟨_, (hnat w).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨(schemePointsHomeomorph B S hS (hV.2.rep.pullback b)).symm t, ?_⟩
      rw [Function.comp_apply, hnat,
        (schemePointsHomeomorph B S hS (hV.2.rep.pullback b)).apply_symm_apply]
  have hpre : Set.range (pointsMap B S hS (yoneda.obj (hV.2.rep.pullback b))
      (yoneda.map (hV.2.rep.snd b))) =
      pointsMap B S hS (yoneda.obj U) b ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι) := by
    have h := preimage_image_pointsMap_of_isPullback B S hS (hV.2.rep.isPullback b) Set.univ
    rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at h
    exact h.symm
  have hAdense : Dense (pointsMap B S hS (yoneda.obj U) b ⁻¹'
      Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    have hEq : Set.range (pointsMap B S hS (yoneda.obj (hV.2.rep.pullback b))
        (yoneda.map (hV.2.rep.snd b))) =
        e ⁻¹' Set.range ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)) := by
      rw [← himage, e.injective.preimage_image]
    rw [← hpre, hEq]
    exact hWdense.preimage e.isOpenMap
  refine dense_iff_inter_open.mpr fun O hO hOne => ?_
  obtain ⟨y, hy⟩ := hOne
  obtain ⟨x, hx⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY U b).mp hsurjb y
  obtain ⟨z, hzO, hzA⟩ := (dense_iff_inter_open.mp hAdense)
    (pointsMap B S hS (yoneda.obj U) b ⁻¹' O) (hO.preimage (continuous_pointsMap B S hS b))
    ⟨x, by rw [Set.mem_preimage, hx]; exact hy⟩
  exact ⟨pointsMap B S hS (yoneda.obj U) b z, hzO, hzA⟩

/-! ### Stacks 0879 -/

/-- If one pullback square over `f` and `g` has an isomorphism as its second projection, so does
any other. -/
private theorem isIso_snd_of_isPullback_of_isIso {C : Type*} [Category C]
    {P Q A B D : C} {fst : P ⟶ A} {snd : P ⟶ B} {fst' : Q ⟶ A} {snd' : Q ⟶ B}
    {f : A ⟶ D} {g : B ⟶ D} (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
    [IsIso snd'] : IsIso snd := by
  rw [← h.isoIsPullback_hom_snd _ _ h']
  infer_instance

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` which is separated, locally of finite type and flat, and let `V ⊆ Y` be an open subspace
such that `f^{-1}V ⟶ V` is an isomorphism and the inclusion of `V` is quasi-compact and
scheme-theoretically dense. Then `f` is an open immersion. -/
@[stacks 0879]
theorem isOpenImmersion_of_isIso_pullback_snd (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V)
    (hsep : IsSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    (hflat : IsFlat B S hS f) (hiso : IsIso (pullback.snd f V.ι))
    (hVqc : IsQuasiCompact B S hS V.ι)
    (hVdense : IsSchemeTheoreticallyDense B S hS V) :
    IsOpenImmersion B S hS f := by
  have hXV : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  have hropen : IsOpenImmersion B S hS (pullback.snd f V.ι) :=
    isOpenImmersion_of_isIso B S hS _
  have hrqf : IsLocallyQuasiFinite B S hS (pullback.snd f V.ι) :=
    isLocallyQuasiFinite_of_isImmersion B S hS _
      (isImmersion_of_isOpenImmersion B S hS hropen)
  have hrlft : IsLocallyOfFiniteType B S hS (pullback.snd f V.ι) :=
    fun U W a b h ha hb hcomm => (hrqf U W a b h ha hb hcomm).1
  have hdimV : HasRelativeDimensionLE 0 B S hS (pullback.snd f V.ι) := fun x =>
    ⟨0, le_rfl, (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
      (pullback.snd f V.ι) hrlft).mp hrqf x⟩
  have hdim := relativeDimensionLE_of_dense_open B S hS hX hY f V hV
    (dense_range_pointsMap_ι_of_isSchemeTheoreticallyDense B S hS hY V hV hVdense)
    hflat hlft 0 hdimV (Or.inr hVqc)
  have hqf : IsLocallyQuasiFinite B S hS f :=
    (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS f hlft).2 fun x => by
      obtain ⟨d, hd, hdx⟩ := hdim x
      simpa [Nat.eq_zero_of_le_zero hd] using hdx
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY hqf hsep
  obtain ⟨U, b, hsurjb, hetaleb⟩ := hY.exists_atlas
  obtain ⟨P, j, a, hpb⟩ := hrep b
  have hEsbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hetale_a : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hetaleb
  have hcomm : yoneda.map j ≫ b = a ≫ f := hpb.w.symm
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map j) :=
    hflat P U a b j hetale_a hetaleb hcomm
  have : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j) :=
    hlft P U a b j hetale_a hetaleb hcomm
  set ePB := hpb.isoIsPullback _ _ (IsPullback.of_hasPullback f b)
  have hePBfac : ePB.hom ≫ pullback.snd f b = yoneda.map j :=
    hpb.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f b)
  have : AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map j) := by
    refine (isSeparated_yoneda_map_iff B S hS j).mp ?_
    have hbc : IsSeparated B S hS (pullback.snd f b) := isSeparated_pullback B S hS f b hsep
    have := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).diagonal ePB.hom (pullback.snd f b) hbc
    rwa [hePBfac] at this
  have hoi : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)) := hV.2.property_snd b
  have hsiteIso : IsIso (pullback.snd j (hV.2.rep.snd b)) := by
    have hleft := ((IsPullback.of_hasPullback j (hV.2.rep.snd b)).map
      (yoneda : BigFppfOver B S hS ⥤ _)).paste_horiz hpb
    rw [← (hV.2.rep.isPullback b).w] at hleft
    have hright := (IsPullback.of_hasPullback (pullback.snd f V.ι) (hV.2.rep.fst b)).paste_horiz
      (IsPullback.of_hasPullback f V.ι)
    have : IsIso (yoneda.map (pullback.snd j (hV.2.rep.snd b))) :=
      isIso_snd_of_isPullback_of_isIso hleft hright
    exact Yoneda.fullyFaithful.isIso_of_isIso_map _
  have hschemeIso : IsIso (pullback.snd ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b))) := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map (pullback.snd j (hV.2.rep.snd b))) :=
      inferInstance
    exact isIso_snd_of_isPullback_of_isIso (IsPullback.of_hasPullback _ _)
      ((IsPullback.of_hasPullback j (hV.2.rep.snd b)).map (BigFppfOver.toScheme B S hS))
  have hres : IsIso ((BigFppfOver.toScheme B S hS).map j ∣_
      ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b)).opensRange) :=
    (Arrow.isIso_hom_iff_isIso_of_isIso
      (morphismRestrictOpensRange ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map (hV.2.rep.snd b))).hom).mpr hschemeIso
  rw [opensRange_snd_eq_chartOpenOfOpenSubspace B S hS V hV
    ⟨CostructuredArrow.mk b, hetaleb⟩] at hres
  have hchart : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    AlgebraicGeometry.isOpenImmersion_of_isIso_morphismRestrict
      ((BigFppfOver.toScheme B S hS).map j)
      (chartOpenOfOpenSubspace B S hS V hV ⟨CostructuredArrow.mk b, hetaleb⟩)
      (isRetrocompactOnCharts_of_isQuasiCompact B S hS V hV hVqc
        ⟨CostructuredArrow.mk b, hetaleb⟩)
      (isSchemeTheoreticallyDenseOnCharts_of_isSchemeTheoreticallyDense B S hS V hV hVdense
        ⟨CostructuredArrow.mk b, hetaleb⟩)
  have hQsbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hq => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      (hsq.map (BigFppfOver.toScheme B S hS)) hq⟩
  have hQj : IsOpenImmersion B S hS (yoneda.map j) :=
    MorphismProperty.relative_map (F := yoneda) hchart
  have hQpb : IsOpenImmersion B S hS (pullback.snd f b) := by
    refine (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ePB.hom (pullback.snd f b)).mp ?_
    rwa [hePBfac]
  have hloc := openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  refine (prop_iff_pullbackSnd_atlas.{u, u} B S hS (openImmersionProperty B S hS)
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    hsurjb hetaleb).2 ?_
  exact (AlgebraicSpaces.hom_pullback_snd_iff B S hS
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk b : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).mpr hQpb

end AlgebraicGeometry.Space

end

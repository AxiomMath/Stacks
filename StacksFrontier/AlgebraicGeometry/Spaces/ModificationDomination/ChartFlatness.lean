module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.Domination
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.RepresentableOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Flatness of the closure of the open part, read on an étale chart

Let `f : X ⟶ Q` be a morphism of algebraic spaces to the space represented by an object `Q` of the
site which is an isomorphism over the open subspace cut out by an open `U₀` of the scheme of `Q`,
and let `u : V ⟶ X` be a surjective étale chart from a scheme with composite `g : V ⟶ Q`. Let `K`
be a sheaf of ideals on `Q` with support exactly `Q ∖ U₀` along which the strict transform of `V`
is flat over the blowup `Q' = Bl_K Q`. Then the scheme-theoretic image of the canonical section of
`X ×_Q Q' ⟶ Q'` over the inverse image of `U₀` is flat over `Q'`.

This is the passage, in the proof of Stacks 087E, from the strict transform of the chart to the
strict transform of the space (Stacks 0863): the base change of that scheme-theoretic image
along the étale chart `V ×_Q Q' ⟶ X ×_Q Q'` is the scheme-theoretic closure of the inverse image
of `U₀` in the scheme `V ×_Q Q'`, which is the strict transform of `V` because the exceptional
divisor lies exactly over `Q ∖ U₀`.

## Main results

* `AlgebraicGeometry.Space.range_modificationSection`: the range of the canonical section is the
  inverse image of the open.
* `AlgebraicGeometry.Space.isFlat_modificationSection_of_flat_strictTransformToBlowUp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` search for presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ChartFlatness :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ChartFlatness
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Range

variable {W T X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The range of the canonical section is the inverse image of the open.** -/
theorem range_modificationSection (f : X ⟶ W) (U : Subfunctor W) [IsIso (pullback.snd f U.ι)]
    (b : T ⟶ W) :
    Subfunctor.range (modificationSection f U b) =
      (U.preimage b).preimage (pullback.snd f b) := by
  refine le_antisymm ?_ ?_
  · rintro A _ ⟨x, rfl⟩
    change (pullback.snd f b).app A ((modificationSection f U b).app A x) ∈ (U.preimage b).obj A
    rw [← NatTrans.comp_app_apply, modificationSection_snd]
    exact x.2
  · set O := (U.preimage b).preimage (pullback.snd f b)
    let t : O.toFunctor ⟶ (U.preimage b).toFunctor := (U.preimage b).fromPreimage _
    have hts : t ≫ modificationSection f U b = O.ι := by
      refine pullback.hom_ext ?_ ?_
      · have hlift : (O.ι ≫ pullback.fst f b) ≫ f =
            (t ≫ U.fromPreimage b) ≫ U.ι := by
          rw [Category.assoc, pullback.condition, Category.assoc, Subfunctor.fromPreimage_ι,
            ← Category.assoc, ← Category.assoc, Subfunctor.fromPreimage_ι]
        have h1 : pullback.lift _ _ hlift ≫ pullback.snd f U.ι = t ≫ U.fromPreimage b :=
          pullback.lift_snd _ _ _
        have h2 : pullback.lift _ _ hlift =
            (t ≫ U.fromPreimage b) ≫ inv (pullback.snd f U.ι) :=
          (IsIso.eq_comp_inv _).2 h1
        have h3 := pullback.lift_fst _ _ hlift
        rw [h2] at h3
        simp only [modificationSection, Category.assoc, pullback.lift_fst] at h3 ⊢
        exact h3
      · rw [Category.assoc, modificationSection_snd, Subfunctor.fromPreimage_ι]
    rw [← Subfunctor.range_ι O, ← hts]
    exact Subfunctor.range_comp_le _ _

end Range

section Chart

/-- The scheme `V ×_Q Bl_K Q`, as an object of the site over `S`. -/
def blowUpChartObj {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_pullback_lt _ _ V.left.property (blowUpObj Q K).left.property)
    (pullback.snd ((BigFppfOver.toScheme B S hS).map g) (_root_.AlgebraicGeometry.blowUpToBase K) ≫
      _root_.AlgebraicGeometry.blowUpToBase K ≫ B.inclusion.map Q.hom)

/-- The first projection `V ×_Q Bl_K Q ⟶ V`. -/
def blowUpChartFst {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData) : blowUpChartObj g K ⟶ V :=
  Over.homMk (ObjectProperty.homMk (pullback.fst _ _)) (by
    apply ObjectProperty.hom_ext
    change pullback.fst ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K) ≫ B.inclusion.map V.hom =
      pullback.snd ((BigFppfOver.toScheme B S hS).map g) (_root_.AlgebraicGeometry.blowUpToBase K) ≫
        _root_.AlgebraicGeometry.blowUpToBase K ≫ B.inclusion.map Q.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    exact congrArg (fun k => pullback.fst ((BigFppfOver.toScheme B S hS).map g)
      (_root_.AlgebraicGeometry.blowUpToBase K) ≫ B.inclusion.map k) (Over.w g).symm)

/-- The second projection `V ×_Q Bl_K Q ⟶ Bl_K Q`. -/
def blowUpChartSnd {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData) :
    blowUpChartObj g K ⟶ blowUpObj Q K :=
  Over.homMk (ObjectProperty.homMk (pullback.snd _ _)) rfl

/-- The square `V ×_Q Bl_K Q` is cartesian in the site. -/
theorem isPullback_blowUpChart {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData) :
    IsPullback (blowUpChartFst g K) (blowUpChartSnd g K) g (blowUpObjHom Q K) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map g)
      (_root_.AlgebraicGeometry.blowUpToBase K))

/-- The open of the chart over the inverse image of `U₀` is the open part of the strict
transform: the exceptional divisor lies exactly over `Q ∖ U₀`. -/
theorem preimage_eq_exceptionalComplement {V Q : BigFppfOver B S hS} (g : V ⟶ Q)
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData)
    (hK : K.supportSet = (U₀ : Set _)ᶜ) :
    (BigFppfOver.toScheme B S hS).map (blowUpChartSnd g K ≫ blowUpObjHom Q K) ⁻¹ᵁ U₀ =
      Stacks.StrictTransform.exceptionalComplement ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K)
        (_root_.AlgebraicGeometry.exceptionalIdeal K) := by
  ext x
  have hmap : (BigFppfOver.toScheme B S hS).map (blowUpChartSnd g K ≫ blowUpObjHom Q K) =
      pullback.snd ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K) ≫ _root_.AlgebraicGeometry.blowUpToBase K :=
    Functor.map_comp _ _ _
  have hsupp : ∀ y, y ∈ K.supportSet ↔ y ∉ (U₀ : Set _) := fun y => by
    rw [hK]
    rfl
  simp only [Stacks.StrictTransform.exceptionalComplement, SetLike.mem_coe,
    hmap]
  rw [Scheme.IdealSheafData.support_comap]
  constructor
  · intro hx hmem
    exact (hsupp _).1 hmem hx
  · intro hx
    by_contra h
    exact hx ((hsupp _).2 h)

/-- **Flatness of the closure of the open part of a modification, read on an étale chart.** -/
theorem isFlat_modificationSection_of_flat_strictTransformToBlowUp {Q : BigFppfOver B S hS}
    (U₀ : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj Q)
    [IsIso (pullback.snd f (openSubspaceOfPoints B S hS (yoneda.obj Q)
      (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))).ι)]
    {V : BigFppfOver B S hS} (u : yoneda.obj V ⟶ X) (hu : IsEtale B S hS u)
    (hus : IsSurjective B S hS u) (g : V ⟶ Q) (hg : u ≫ f = yoneda.map g)
    (K : ((BigFppfOver.toScheme B S hS).obj Q).IdealSheafData)
    (hK : K.supportSet = (U₀ : Set _)ᶜ)
    (hflat : Flat (strictTransformToBlowUp ((BigFppfOver.toScheme B S hS).map g) K))
    (hqc : IsQuasiCompact B S hS ((openSubspaceOfPoints B S hS (yoneda.obj Q)
      (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))).preimage (yoneda.map (blowUpObjHom Q K))).ι) :
    IsFlat B S hS ((schemeTheoreticImageSubfunctor B S hS (modificationSection f
        (openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _)))
        (yoneda.map (blowUpObjHom Q K)))).ι ≫
      pullback.snd f (yoneda.map (blowUpObjHom Q K))) := by
  set U := openSubspaceOfPoints B S hS (yoneda.obj Q) (pointsToScheme B S hS Q ⁻¹' (U₀ : Set _))
    with hUdef
  set b := yoneda.map (blowUpObjHom Q K) with hbdef
  have hQ := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Q
  have hP := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpObj Q K)
  have hVP := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (blowUpChartObj g K)
  have hY : IsAlgebraicSpace B S hS (pullback f b) := isAlgebraicSpace_pullback B S hS f b hX hP hQ
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_preimage_pointsToScheme Q U₀
  have hsq := isPullback_blowUpChart g K
  have hsqY : IsPullback (yoneda.map (blowUpChartFst g K)) (yoneda.map (blowUpChartSnd g K))
      (yoneda.map g) b := hsq.map yoneda
  have hw : (yoneda.map (blowUpChartFst g K) ≫ u) ≫ f = yoneda.map (blowUpChartSnd g K) ≫ b := by
    rw [Category.assoc, hg, hsqY.w]
  set c : yoneda.obj (blowUpChartObj g K) ⟶ pullback f b :=
    pullback.lift (yoneda.map (blowUpChartFst g K) ≫ u) (yoneda.map (blowUpChartSnd g K)) hw
    with hcdef
  have hcsnd : c ≫ pullback.snd f b = yoneda.map (blowUpChartSnd g K) := pullback.lift_snd _ _ _
  have hc : IsPullback c (yoneda.map (blowUpChartFst g K)) (pullback.fst f b) u := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f b).flip
    rw [hcsnd, hg]
    exact hsqY.flip
  have hcE : IsEtale B S hS c := isEtale_of_isPullback_yoneda B S hS hc.flip hu
  have hcS : IsSurjective B S hS c := surjective_pointsMap_of_isPullback B S hS hc.flip hus
  have hU' : IsOpenSubspace B S hS (U.preimage b) := isOpenSubspace_preimage B S hS b U hQ hP hU
  have hO : IsOpenSubspace B S hS ((U.preimage b).preimage (pullback.snd f b)) :=
    isOpenSubspace_preimage B S hS (pullback.snd f b) _ hP hY hU'
  have hOqc : IsQuasiCompact B S hS ((U.preimage b).preimage (pullback.snd f b)).ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage _ _) hqc
  have himg : schemeTheoreticImageSubfunctor B S hS (modificationSection f U b) =
      schemeTheoreticClosure B S hS ((U.preimage b).preimage (pullback.snd f b)) :=
    schemeTheoreticImageSubfunctor_congr_range' B S hS _ _ hY
      (by rw [range_modificationSection, Subfunctor.range_ι])
  have hOc : ((U.preimage b).preimage (pullback.snd f b)).preimage c =
      Subfunctor.range (yoneda.map (openSubHom (blowUpChartObj g K)
        ((BigFppfOver.toScheme B S hS).map (blowUpChartSnd g K ≫ blowUpObjHom Q K) ⁻¹ᵁ U₀))) := by
    rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, hcsnd, hbdef,
      ← Functor.map_comp, hUdef, openSubspaceOfPoints_preimage_yoneda_map,
      openSubspaceOfPoints_preimage_pointsToScheme]
  have hpre : (schemeTheoreticImageSubfunctor B S hS (modificationSection f U b)).preimage c =
      (closedSubspaceOfIdeal (blowUpChartObj g K)
        (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
          (_root_.AlgebraicGeometry.blowUpToBase K)
          (_root_.AlgebraicGeometry.exceptionalIdeal K))).1 := by
    rw [himg, ← schemeTheoreticClosure_preimage_of_isEtale B S hS hY _ hO hOqc hVP c hcE, hOc,
      schemeTheoreticClosure, schemeTheoreticImageSubfunctor_congr_range' B S hS _ _ hVP
        (Subfunctor.range_ι _), schemeTheoreticImageSubfunctor_yoneda_openSubHom,
      preimage_eq_exceptionalComplement g U₀ K hK]
    exact congrArg (fun J => (closedSubspaceOfIdeal (blowUpChartObj g K) J).1)
      (Stacks.StrictTransform.ideal_eq_ker_ι _ _ _).symm
  set X' := schemeTheoreticImageSubfunctor B S hS (modificationSection f U b) with hX'def
  have hX'cl : IsClosedSubspace B S hS X' :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _ hY
  have hZcl : IsClosedSubspace B S hS (X'.preimage c) :=
    isClosedSubspace_preimage B S hS c X' hY hVP hX'cl
  have hsq' : IsPullback (X'.fromPreimage c) (X'.preimage c).ι X'.ι c :=
    Subfunctor.isPullback_preimage c X'
  have hc'E : IsEtale B S hS (X'.fromPreimage c) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq' hZcl.1 hX'cl.1 hVP hY hcE
  have hc'S : IsSurjective B S hS (X'.fromPreimage c) :=
    surjective_pointsMap_of_isPullback B S hS hsq'.flip hcS
  have hcomp : X'.fromPreimage c ≫ X'.ι ≫ pullback.snd f b =
      (X'.preimage c).ι ≫ yoneda.map (blowUpChartSnd g K) := by
    rw [← Category.assoc, hsq'.w, Category.assoc, hcsnd]
  refine isFlat_of_comp_of_isSurjective_of_isFlat B S hS hZcl.1 hX'cl.1 _ _ hc'S
    (isFlat_of_isEtale B S hS hc'E) ?_
  rw [hcomp]
  have key : ∀ Z : Subfunctor (yoneda.obj (blowUpChartObj g K)),
      Z = (closedSubspaceOfIdeal (blowUpChartObj g K)
        (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
          (_root_.AlgebraicGeometry.blowUpToBase K)
          (_root_.AlgebraicGeometry.exceptionalIdeal K))).1 →
      IsFlat B S hS (Z.ι ≫ yoneda.map (blowUpChartSnd g K)) := by
    rintro Z rfl
    set j := closedSubschemeOverι B S hS (blowUpChartObj g K)
      (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K)
        (_root_.AlgebraicGeometry.exceptionalIdeal K)) with hjdef
    have : Mono j := (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono (Stacks.StrictTransform.ideal ((BigFppfOver.toScheme B S hS).map g)
        (_root_.AlgebraicGeometry.blowUpToBase K)
        (_root_.AlgebraicGeometry.exceptionalIdeal K)).subschemeι))
    have hmono : Mono (yoneda.map j) := Functor.map_mono yoneda j
    have hiso : IsIso (Subfunctor.toRange (yoneda.map j)) := inferInstance
    have hι : (Subfunctor.range (yoneda.map j)).ι = inv (Subfunctor.toRange (yoneda.map j)) ≫
        yoneda.map j := (IsIso.eq_inv_comp _).2 (Subfunctor.toRange_ι _).symm
    have hflat' : Flat ((BigFppfOver.toScheme B S hS).map (j ≫ blowUpChartSnd g K)) := by
      rw [Functor.map_comp]
      exact hflat
    change IsFlat B S hS ((Subfunctor.range (yoneda.map j)).ι ≫ yoneda.map (blowUpChartSnd g K))
    rw [hι, Category.assoc, ← Functor.map_comp]
    exact isFlat_comp B S hS (closedSubspaceOfIdeal (blowUpChartObj g K) _).2.1
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) hP _ _
      (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS (inv (Subfunctor.toRange (yoneda.map j)))))
      (isFlat_yoneda_map B S hS _ hflat')
  exact key _ hpre

end Chart

end AlgebraicGeometry.Space

end

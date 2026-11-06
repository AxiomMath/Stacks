module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Morphisms of modules along a limit of quasi-compact quasi-separated schemes

Let `T` be a cofiltered system of schemes over `S` with affine transition morphisms and a limit
`c` of the underlying schemes, and let `T i₀` be quasi-compact and quasi-separated. A morphism
between the inverse images to `h_{c.pt}` of two quasi-coherent modules of finite presentation on
`h_{T i₀}` is, at some stage `j ⟶ i₀`, the inverse image of a morphism between their inverse
images to `h_{T j}`.

## Main results

* `AlgebraicGeometry.Space.isPullback_postPullbackSystem_map`: the transition morphisms of a system
  of base changes are base changes of those of the system.
* `AlgebraicGeometry.Space.exists_homTransport_schemeSpaceMap_eq_of_isLimit`: the statement
  above.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR), part (2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

attribute [local instance] IsCofiltered.isConnected preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] (T : I ⥤ BigFppfOver B S hS) (i₀ : I)

/-! ### Systems of base changes -/

section BaseChange

variable {U₀ : BigFppfOver B S hS} (p : U₀ ⟶ T.obj i₀)

/-- **The transition morphisms of a system of base changes are base changes** of the transition
morphisms of the system. -/
theorem isPullback_postPullbackSystem_map {k k' : Over i₀} (f : k ⟶ k') :
    IsPullback ((postPullbackSystem T i₀ p).map f) (pullback.fst ((Over.post T).obj k).hom p)
      (pullback.fst ((Over.post T).obj k').hom p) (T.map f.left) := by
  refine IsPullback.of_right ?_ (postPullbackSystem_map_fst T i₀ f)
    (IsPullback.of_hasPullback ((Over.post T).obj k').hom p).flip
  have hw : T.map f.left ≫ ((Over.post T).obj k').hom = ((Over.post T).obj k).hom :=
    Over.w ((Over.post T).map f)
  rw [postPullbackSystem_map_snd]
  exact (congrArg (IsPullback (pullback.snd ((Over.post T).obj k).hom p)
    (pullback.fst ((Over.post T).obj k).hom p) p) hw).mpr (IsPullback.of_hasPullback _ p).flip

variable [∀ {i j : I} (e : i ⟶ j),
  _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (T.map e))]

/-- The transition morphisms of a system of base changes are affine. -/
instance isAffineHom_postPullbackSystem_map {k k' : Over i₀} (f : k ⟶ k') :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map ((postPullbackSystem T i₀ p).map f)) :=
  MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
    ((isPullback_postPullbackSystem_map T i₀ p f).map (BigFppfOver.toScheme B S hS)).flip
    (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (T.map f.left))))

/-- The projection `T j ×_{T i₀} U₀ ⟶ U₀` is affine. -/
theorem isAffineHom_toScheme_postPullbackSystem_snd (k : Over i₀) :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (pullback.snd ((Over.post T).obj k).hom p)) :=
  MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
    ((IsPullback.of_hasPullback ((Over.post T).obj k).hom p).map
      (BigFppfOver.toScheme B S hS))
    (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (T.map k.hom))))

/-- Every stage of the system of base changes of an affine `U₀` is affine. -/
instance isAffine_postPullbackSystem_obj [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    (k : Over i₀) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((postPullbackSystem T i₀ p).obj k)) :=
  have := isAffineHom_toScheme_postPullbackSystem_snd T i₀ p k
  isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (pullback.snd _ p))

/-- Every stage of the system of base changes of a quasi-compact `U₀` is quasi-compact. -/
instance compactSpace_postPullbackSystem_obj [CompactSpace ((BigFppfOver.toScheme B S hS).obj U₀)]
    (k : Over i₀) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj ((postPullbackSystem T i₀ p).obj k)) :=
  have := isAffineHom_toScheme_postPullbackSystem_snd T i₀ p k
  QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (pullback.snd ((Over.post T).obj k).hom p))

end BaseChange

/-! ### Morphisms of systems of base changes -/

section PairMap

variable {U₀ R₀ : BigFppfOver B S hS} (p : U₀ ⟶ T.obj i₀) {q : R₀ ⟶ T.obj i₀} (g : R₀ ⟶ U₀)
  (hg : g ≫ p = q)

/-- The morphism `T j ×_{T i₀} R₀ ⟶ T j ×_{T i₀} U₀` induced by a morphism `g : R₀ ⟶ U₀` over
`T i₀`. -/
noncomputable def baseChangePairMap (k : Over i₀) :
    (postPullbackSystem T i₀ q).obj k ⟶ (postPullbackSystem T i₀ p).obj k :=
  pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id, hg])

/-- `baseChangePairMap` commutes with the projections to `T j`. -/
theorem baseChangePairMap_fst (k : Over i₀) :
    baseChangePairMap T i₀ p g hg k ≫ pullback.fst ((Over.post T).obj k).hom p =
      pullback.fst ((Over.post T).obj k).hom q :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `baseChangePairMap` followed by the projection to `U₀` is the projection to `R₀` followed by
`g`. -/
theorem baseChangePairMap_snd (k : Over i₀) :
    baseChangePairMap T i₀ p g hg k ≫ pullback.snd ((Over.post T).obj k).hom p =
      pullback.snd ((Over.post T).obj k).hom q ≫ g :=
  pullback.lift_snd _ _ _

/-- The morphisms `baseChangePairMap` form a morphism of systems: they commute with the transition
morphisms. -/
theorem postPullbackSystem_map_comp_baseChangePairMap {k k' : Over i₀} (f : k ⟶ k') :
    (postPullbackSystem T i₀ q).map f ≫ baseChangePairMap T i₀ p g hg k' =
      baseChangePairMap T i₀ p g hg k ≫ (postPullbackSystem T i₀ p).map f :=
  pullback.hom_ext
    (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangePairMap_fst T i₀ p g hg k')).trans (postPullbackSystem_map_fst T i₀ f))).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (postPullbackSystem_map_fst T i₀ f)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (baseChangePairMap_fst T i₀ p g hg k))))).symm)
    (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangePairMap_snd T i₀ p g hg k')).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ g) (postPullbackSystem_map_snd T i₀ f))))).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (postPullbackSystem_map_snd T i₀ f)).trans
          (baseChangePairMap_snd T i₀ p g hg k))).symm)

variable (c : Cone T)

/-- The morphism `c.pt ×_{T i₀} R₀ ⟶ c.pt ×_{T i₀} U₀` induced by `g`. -/
noncomputable def postPullbackConePairMap :
    (postPullbackCone T c i₀ q).pt ⟶ (postPullbackCone T c i₀ p).pt :=
  pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id, hg])

/-- `postPullbackConePairMap` commutes with the projections to `c.pt`. -/
theorem postPullbackConePairMap_fst :
    postPullbackConePairMap T i₀ p g hg c ≫ pullback.fst ((Over.conePost T i₀).obj c).pt.hom p =
      pullback.fst ((Over.conePost T i₀).obj c).pt.hom q :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `postPullbackConePairMap` followed by the projection to `U₀` is the projection to `R₀`
followed by `g`. -/
theorem postPullbackConePairMap_snd :
    postPullbackConePairMap T i₀ p g hg c ≫ pullback.snd ((Over.conePost T i₀).obj c).pt.hom p =
      pullback.snd ((Over.conePost T i₀).obj c).pt.hom q ≫ g :=
  pullback.lift_snd _ _ _

/-- `postPullbackConePairMap` and the morphisms `baseChangePairMap` commute with the projections
of the base-changed cones. -/
theorem postPullbackCone_π_app_comp_baseChangePairMap (k : Over i₀) :
    (postPullbackCone T c i₀ q).π.app k ≫ baseChangePairMap T i₀ p g hg k =
      postPullbackConePairMap T i₀ p g hg c ≫ (postPullbackCone T c i₀ p).π.app k :=
  pullback.hom_ext
    (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangePairMap_fst T i₀ p g hg k)).trans (postPullbackCone_π_app_fst T i₀ c k))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (postPullbackCone_π_app_fst T i₀ c k)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ _) (postPullbackConePairMap_fst T i₀ p g hg c))))).symm)
    (((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        (baseChangePairMap_snd T i₀ p g hg k)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ g) (postPullbackCone_π_app_snd T i₀ c k))))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (postPullbackCone_π_app_snd T i₀ c k)).trans
            (postPullbackConePairMap_snd T i₀ p g hg c))).symm)

/-- **The base change of a kernel pair is a kernel pair of each base change.** -/
theorem isPullback_baseChangePairMap {s₀ t₀ : R₀ ⟶ U₀} (hk : IsPullback s₀ t₀ p p)
    (hs : s₀ ≫ p = q) (ht : t₀ ≫ p = q) (k : Over i₀) :
    IsPullback (baseChangePairMap T i₀ p s₀ hs k) (baseChangePairMap T i₀ p t₀ ht k)
      (pullback.fst ((Over.post T).obj k).hom p) (pullback.fst ((Over.post T).obj k).hom p) := by
  refine IsPullback.of_isPullback_kernelPair hk
    (IsPullback.of_hasPullback ((Over.post T).obj k).hom p).flip
    (ρ := pullback.snd ((Over.post T).obj k).hom q) (baseChangePairMap_snd T i₀ p s₀ hs k)
    (baseChangePairMap_snd T i₀ p t₀ ht k)
    (by rw [baseChangePairMap_fst, baseChangePairMap_fst]) ?_
  rw [baseChangePairMap_fst, hs]
  exact (IsPullback.of_hasPullback _ q).flip

end PairMap

/-! ### Fullness along a limit of quasi-compact quasi-separated schemes -/

set_option synthInstance.maxHeartbeats 200000 in
/-- **A morphism of inverse images to the limit descends to a stage**, for a cofiltered system
of schemes with affine transition morphisms whose stage `T i₀` is quasi-compact and
quasi-separated (Stacks 01ZR (2), read on the represented algebraic spaces). -/
theorem exists_homTransport_schemeSpaceMap_eq_of_isLimit (hZ : B.Contains (⊤_ Scheme.{u}))
    [IsCofiltered I]
    [∀ {i j : I} (e : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (T.map e))]
    (c : Cone T) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hqc : IsQuasiCompactSpace B S hS (schemeSpace (T.obj i₀)).1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (schemeSpace (T.obj i₀)).1)
    {G H : Modules.{u, u} B S hS (schemeSpace (T.obj i₀)).1 (schemeSpace (T.obj i₀)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (schemeSpaceMap (U := c.pt) (c.π.app i₀))).obj G ⟶
      (modulePullback B S hS (schemeSpaceMap (U := c.pt) (c.π.app i₀))).obj H) :
    ∃ (k : Over i₀) (ψ : (modulePullback B S hS (schemeSpaceMap (T.map k.hom))).obj G ⟶
        (modulePullback B S hS (schemeSpaceMap (T.map k.hom))).obj H),
      homTransport G H (schemeSpaceMap (U := c.pt) (c.π.app k.left))
        (schemeSpaceMap_cone_π_comp T c k.hom) ψ = φ := by
  change IsQuasiCompactSpace B S hS (yoneda.obj (T.obj i₀)) at hqc
  change IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (T.obj i₀)) at hqs
  obtain ⟨U₀, a₀, hU₀, hs₀, ha₀'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj (T.obj i₀))
      (isAlgebraicSpace_yoneda B S hS (T.obj i₀))).mp hqc
  have ha₀ := (isEtale_iff_presheaf_of_yoneda B S hS a₀).mp ha₀'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀
  obtain ⟨W, hW, ⟨eW⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ
    (yoneda.obj (T.obj i₀)) (isAlgebraicSpace_yoneda B S hS (T.obj i₀))).mp hqs U₀ U₀ a₀ a₀ hU₀ hU₀
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := hW
  let w₀ : U₀ ⟶ T.obj i₀ := Yoneda.fullyFaithful.preimage a₀
  have hw₀ : yoneda.map w₀ = a₀ := Yoneda.fullyFaithful.map_preimage _
  let s₀ : W ⟶ U₀ := Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.fst a₀ a₀)
  let t₀ : W ⟶ U₀ := Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.snd a₀ a₀)
  have hk' : IsPullback (yoneda.map s₀) (yoneda.map t₀) (yoneda.map w₀) (yoneda.map w₀) := by
    rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage, hw₀]
    exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩
      eW rfl rfl
  have hk : IsPullback s₀ t₀ w₀ w₀ := IsPullback.of_map yoneda
    (Yoneda.fullyFaithful.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact hk'.w))
    hk'
  have hts : t₀ ≫ w₀ = s₀ ≫ w₀ := hk.w.symm
  have hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have he : ∀ k : Over i₀, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (pullback.fst ((Over.post T).obj k).hom w₀)) := fun k =>
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback ((Over.post T).obj k).hom w₀).map yoneda).flip (hw₀ ▸ ha₀)
  have hsu : ∀ k : Over i₀, (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (pullback.fst ((Over.post T).obj k).hom w₀)) := fun k =>
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback ((Over.post T).obj k).hom w₀).map yoneda).flip (hw₀ ▸ hs₀)
  have hec : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (pullback.fst ((Over.conePost T i₀).obj c).pt.hom w₀)) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback ((Over.conePost T i₀).obj c).pt.hom w₀).map yoneda).flip
      (hw₀ ▸ ha₀)
  have hsc : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (pullback.fst ((Over.conePost T i₀).obj c).pt.hom w₀)) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback ((Over.conePost T i₀).obj c).pt.hom w₀).map yoneda).flip
      (hw₀ ▸ hs₀)
  have hu : ∀ {k k' : Over i₀} (f : k ⟶ k'), (postPullbackSystem T i₀ w₀).map f ≫
      pullback.fst ((Over.post T).obj k').hom w₀ ≫ T.map k'.hom =
        pullback.fst ((Over.post T).obj k).hom w₀ ≫ T.map k.hom := fun {k k'} f =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (postPullbackSystem_map_fst T i₀ f)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w ((Over.post T).map f)))))
  exact exists_homTransport_eq_of_charts (Y := fun k : Over i₀ => schemeSpace (T.obj k.left))
    (fun k => schemeSpaceMap (T.map k.hom)) (fun k => schemeSpaceMap (U := c.pt) (c.π.app k.left))
    (fun k => schemeSpaceMap_cone_π_comp T c k.hom)
    (postPullbackCone T c i₀ w₀) (isLimitPostPullbackCone T c i₀ w₀ hc)
    (fun k => schemeSpaceMap (pullback.fst ((Over.post T).obj k).hom w₀))
    (schemeSpaceMap (pullback.fst ((Over.conePost T i₀).obj c).pt.hom w₀))
    (fun {k k'} f => ObjectProperty.hom_ext _ ((congrArg (_ ≫ ·) (yoneda.map_comp _ _).symm).trans
      ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (hu f)).trans
        (yoneda.map_comp _ _)))))
    (fun k => ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map (postPullbackCone_π_app_fst T i₀ c k).symm).trans
        (yoneda.map_comp _ _))))
    (fun k => (isEtale_iff_presheaf_of_yoneda B S hS _).2 (he k))
    (fun k => isEtaleCovering_atlas B S hS (schemeSpace (T.obj k.left)).2 (hsu k) (he k))
    (isEtaleCovering_atlas B S hS (schemeSpace c.pt).2 hsc hec)
    (postPullbackCone T c i₀ (s₀ ≫ w₀)) (isLimitPostPullbackCone T c i₀ (s₀ ≫ w₀) hc)
    (fun k => schemeSpaceMap (baseChangePairMap T i₀ w₀ s₀ rfl k))
    (fun k => schemeSpaceMap (baseChangePairMap T i₀ w₀ t₀ hts k))
    (schemeSpaceMap (postPullbackConePairMap T i₀ w₀ s₀ rfl c))
    (schemeSpaceMap (postPullbackConePairMap T i₀ w₀ t₀ hts c))
    (fun f => ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map (postPullbackSystem_map_comp_baseChangePairMap T i₀ w₀ s₀ rfl f)).trans
        (yoneda.map_comp _ _))))
    (fun f => ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map (postPullbackSystem_map_comp_baseChangePairMap T i₀ w₀ t₀ hts f)).trans
        (yoneda.map_comp _ _))))
    (fun k => ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map
        (postPullbackCone_π_app_comp_baseChangePairMap T i₀ w₀ s₀ rfl c k)).trans
        (yoneda.map_comp _ _))))
    (fun k => ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map
        (postPullbackCone_π_app_comp_baseChangePairMap T i₀ w₀ t₀ hts c k)).trans
        (yoneda.map_comp _ _))))
    (ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
      ((postPullbackConePairMap_fst T i₀ w₀ s₀ rfl c).trans
        (postPullbackConePairMap_fst T i₀ w₀ t₀ hts c).symm)).trans (yoneda.map_comp _ _))))
    (fun k => (isPullback_baseChangePairMap T i₀ w₀ hk rfl hts k).map yoneda)
    hG hGfp hH hHfp φ

end AlgebraicGeometry.Space

end

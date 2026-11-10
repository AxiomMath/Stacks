module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationAtlasBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentChartLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Proper support descends along a limit of affine schemes

Let `T` be a directed inverse system of affine schemes over `S` with limit `c.pt` in the site,
let `X₀` be an algebraic space over `S`, and write `X_V = h_V ⨯ X₀` for the base change of `X₀`
to a scheme `V` over `S`. For a quasi-coherent module `G` of finite type on `X_{T j₀}` whose
pullback to `X_{c.pt}` has support proper over `c.pt`, the pullback of `G` to `X_{T j}` has support
proper over `T j` for some `j ≥ j₀`. This is the content of Stacks 70.12.3 (08K2) in the
situation used for Noetherian approximation, where the index set is that of the finite subsets of
a ring and need not be small compared to the cofinality of the site's cutoff.

## Main definitions

* `AlgebraicGeometry.Space.productMorphismDescentData`: the situation of Stacks 084W attached to
  `X_{T j₀} ⟶ h_{T j₀}`, with base the system `h_{T j}`.

## Main results

* `AlgebraicGeometry.Space.exists_hasProperSupport_productSpaceMap`: the descent of proper
  support.

## Implementation notes

The situation of Stacks 084W is a `AlgebraicGeometry.Space.MorphismDescentSituation`, whose
chart limits are contained in the site because the limit of the system is
(`AlgebraicGeometry.Space.HasContainedChartLimits.of_isLimit_toScheme`), so that it satisfies
the convention of tag 07SD
(`AlgebraicGeometry.Space.HasContainedChartLimits.siteContainsBaseChangeLimits`) and Stacks 08K2
applies to it in the form
`exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits`; no bound on the
size of the index set enters. Its stages and its limit are identified with the base changes
`X_{T j}` and `X_{c.pt}`, and Stacks 08K2 for it is transported along these identifications by
Stacks 0CZF and Stacks 07TZ part (3).

## References

* [Stacks Project, Tag 08K2](https://stacks.math.columbia.edu/tag/08K2)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Properness over the base of a closed subset depends only on the subset. -/
theorem IsProperOver.of_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX : IsAlgebraicSpace B S hS X} {hY : IsAlgebraicSpace B S hS Y} {f : X ⟶ Y}
    {hf : IsLocallyOfFiniteType B S hS f} {T T' : Set (points B S hS X)} (h : T = T')
    {hT : IsClosed T} (hT' : IsClosed T') (hp : IsProperOver B S hS hX hY f hf T hT) :
    IsProperOver B S hS hX hY f hf T' hT' := by
  subst h
  exact hp

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] (hZ : B.Contains (⊤_ Scheme.{u}))
  (T : Jᵒᵖ ⥤ BigFppfOver B S hS) [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
  {c : Cone T} (hc : IsLimit c) (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (X₀ : AlgebraicSpaces B S hS) (j₀ : J)
  (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj (op j₀))).1)
  (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (productSpace X₀ (T.obj (op j₀))).1)

/-- **The situation of Stacks 084W attached to a base change along a limit of affine
schemes.** The base is the system of the `h_{T j}`, whose limit `h_{c.pt}` is an algebraic space
and whose chart limits are contained in the site since `c.pt` is; the morphism over the stage
`j₀` is the projection `X_{T j₀} ⟶ h_{T j₀}`, its target being the stage itself. -/
noncomputable def productMorphismDescentData : MorphismDescentSituation B S hS hZ J where
  base := T ⋙ yoneda
  base_isAlgebraicSpace i := isAlgebraicSpace_yoneda B S hS (T.obj (op i))
  transition_affine a := isAffineHom_yoneda_map B S hS (T.map a)
  limit_isAlgebraicSpace := (isAlgebraicSpace_yoneda B S hS c.pt).of_iso
    ((isLimitOfPreserves yoneda hc).conePointUniqueUpToIso (limit.isLimit _))
  initial := j₀
  source₀ := (productSpace X₀ (T.obj (op j₀))).1
  target₀ := yoneda.obj (T.obj (op j₀))
  sourceToBase := (productSpaceFst X₀ (T.obj (op j₀))).hom
  targetToBase := 𝟙 _
  map₀ := (productSpaceFst X₀ (T.obj (op j₀))).hom
  map₀_over := Category.comp_id _
  source₀_isAlgebraicSpace := (productSpace X₀ (T.obj (op j₀))).2
  target₀_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  base₀_quasiCompact := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ inferInstance
  base₀_quasiSeparated := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
    ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩
  source₀_quasiCompact := hqc
  source₀_quasiSeparated := hqs
  target₀_quasiCompact := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ inferInstance
  target₀_quasiSeparated := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
    ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩

include hcS in
/-- **The product situation satisfies the convention of tag 07SD.** The limits of the affine
charts of the system `h_{T j}` are contained in the site, because the limit `c.pt` of the system
is (`AlgebraicGeometry.Space.HasContainedChartLimits.of_isLimit_toScheme`). -/
theorem siteContainsBaseChangeLimits_productMorphismDescentData :
    haveI : Nonempty J := ⟨j₀⟩
    haveI : IsFiltered J := inferInstance
    SiteContainsBaseChangeLimits B S hS
      (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).base :=
  have : Nonempty J := ⟨j₀⟩
  have : IsDirectedOrder J := inferInstance
  have : IsFiltered J := inferInstance
  (HasContainedChartLimits.of_relocalize hZ (HasContainedChartLimits.of_iso
    (Functor.isoWhiskerLeft T (OverShriek.relocalizeYonedaIso (integersMap B S hS hZ)))
    (HasContainedChartLimits.of_isLimit_toScheme (T ⋙ Over.map (integersMap B S hS hZ))
      (c := (Over.map (integersMap B S hS hZ)).mapCone c) hcS))).siteContainsBaseChangeLimits

/-- The target `Y_i` of a stage of the product situation, as an algebraic space. -/
noncomputable abbrev productTargetAtSpace (i : J) (hi : j₀ ≤ i) : AlgebraicSpaces B S hS :=
  ⟨(productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).targetAt i hi,
    (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).targetAt_isAlgebraicSpace i hi⟩

/-- The target `Y` at the limit of the product situation, as an algebraic space. -/
noncomputable abbrev productTargetLimitSpace : AlgebraicSpaces B S hS :=
  ⟨(productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).targetLimit,
    (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).targetLimit_isAlgebraicSpace⟩

/-- **The stage `X_i` of the product situation is the base change `X_{T i}`.** -/
noncomputable def productSourceAtIso (i : J) (hi : j₀ ≤ i) :
    productSpace X₀ (T.obj (op i)) ≅
      (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceAtSpace i hi :=
  ObjectProperty.isoMk _
    (pullbackProdFstIsoProd (yoneda.map (T.map (homOfLE hi).op)) X₀.1).symm

/-- The identification `productSourceAtIso` of the stage `X_i` with `X_{T i}` is compatible with
the maps to `X_{T j₀}`. -/
theorem productSourceAtIso_hom_comp (i : J) (hi : j₀ ≤ i) :
    (productSourceAtIso hZ T hc X₀ j₀ hqc hqs i hi).hom ≫
        (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceAtToSource₀ i hi =
      productSpaceMap X₀ (T.map (homOfLE hi).op) := by
  apply ObjectProperty.hom_ext
  change (pullbackProdFstIsoProd (yoneda.map (T.map (homOfLE hi).op)) X₀.1).inv ≫
      pullback.snd (yoneda.map (T.map (homOfLE hi).op))
        (prod.fst : yoneda.obj (T.obj (op j₀)) ⨯ X₀.1 ⟶ _) =
    prod.map (yoneda.map (T.map (homOfLE hi).op)) (𝟙 X₀.1)
  apply prod.hom_ext <;> simp

/-- The section `h_{T i} ⟶ h_{T i} ×_{h_{T j₀}} h_{T j₀}` of the first projection. -/
noncomputable def stageTargetLift (i : J) (hi : j₀ ≤ i) :
    yoneda.obj (T.obj (op i)) ⟶
      pullback (yoneda.map (T.map (homOfLE hi).op)) (𝟙 (yoneda.obj (T.obj (op j₀)))) :=
  pullback.lift (𝟙 _) (yoneda.map (T.map (homOfLE hi).op)) (by simp)

/-- The section `stageTargetLift` is an isomorphism. -/
instance (i : J) (hi : j₀ ≤ i) : IsIso (stageTargetLift T j₀ i hi) :=
  have : IsIso (stageTargetLift T j₀ i hi ≫ pullback.fst (yoneda.map (T.map (homOfLE hi).op))
      (𝟙 (yoneda.obj (T.obj (op j₀))))) := by
    rw [stageTargetLift, pullback.lift_fst]; infer_instance
  IsIso.of_isIso_comp_right _ (pullback.fst _ _)

/-- The comparison `h_{T i} ⟶ Y_i` with the target of a stage of the product situation. -/
noncomputable def productTargetAtHom (i : J) (hi : j₀ ≤ i) :
    schemeSpace (T.obj (op i)) ⟶ productTargetAtSpace hZ T hc X₀ j₀ hqc hqs i hi :=
  ObjectProperty.homMk (stageTargetLift T j₀ i hi)

/-- The comparison `productTargetAtHom` is an isomorphism. -/
instance (i : J) (hi : j₀ ≤ i) : IsIso (productTargetAtHom hZ T hc X₀ j₀ hqc hqs i hi) := by
  have h' : IsIso ((ObjectProperty.ι _).map (productTargetAtHom hZ T hc X₀ j₀ hqc hqs i hi)) :=
    inferInstanceAs (IsIso (stageTargetLift T j₀ i hi))
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- The square comparing a stage of the product situation with the base change `X_{T i}`. -/
theorem isPullback_productSourceAtIso (i : J) (hi : j₀ ≤ i) :
    IsPullback (productSourceAtIso hZ T hc X₀ j₀ hqc hqs i hi).hom
      (productSpaceFst X₀ (T.obj (op i)))
      (ObjectProperty.homMk ((productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).mapAt i hi) :
        (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceAtSpace i hi ⟶
          productTargetAtSpace hZ T hc X₀ j₀ hqc hqs i hi)
      (productTargetAtHom hZ T hc X₀ j₀ hqc hqs i hi) := by
  refine IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ ?_⟩
  dsimp only [productSourceAtIso, productTargetAtHom, stageTargetLift, productSpaceFst,
    MorphismDescentSituation.mapAt, MorphismDescentSituation.baseAtToInitial,
    productMorphismDescentData,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.isoMk_hom, Iso.symm_hom, Functor.comp_map, ObjectProperty.homMk,
    ObjectProperty.isoMk]
  refine pullback.hom_ext (f := yoneda.map (T.map (homOfLE hi).op))
    (g := 𝟙 (yoneda.obj (T.obj (op j₀)))) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((pullbackProdFstIsoProd_inv_fst (yoneda.map (T.map (homOfLE hi).op)) X₀.1).trans
        ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).symm.trans
          (Category.assoc _ _ _).symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((pullbackProdFstIsoProd_inv_snd_fst (yoneda.map (T.map (homOfLE hi).op)) X₀.1).trans
        ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).symm.trans (Category.assoc _ _ _).symm)))

/-- The limit of the base system `h_{T j}` is `h_{c.pt}`. -/
noncomputable def productLimitIso :
    yoneda.obj c.pt ≅ limit (T ⋙ yoneda) :=
  (isLimitOfPreserves yoneda hc).conePointUniqueUpToIso (limit.isLimit _)

omit [IsDirected J (· ≤ ·)] [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))] in
/-- The isomorphism `productLimitIso` followed by the projection to `h_{T j}` is the map induced
by `c.pt ⟶ T j`. -/
theorem productLimitIso_hom_π (j : Jᵒᵖ) :
    (productLimitIso T hc).hom ≫ limit.π (T ⋙ yoneda) j = yoneda.map (c.π.app j) :=
  (isLimitOfPreserves yoneda hc).conePointUniqueUpToIso_hom_comp (limit.isLimit _) j

omit [IsDirected J (· ≤ ·)] [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))] in
/-- The inverse of `productLimitIso` followed by the map induced by `c.pt ⟶ T j` is the projection
to `h_{T j}`. -/
theorem productLimitIso_inv_map (j : Jᵒᵖ) :
    (productLimitIso T hc).inv ≫ yoneda.map (c.π.app j) = limit.π (T ⋙ yoneda) j := by
  rw [← productLimitIso_hom_π T hc j, Iso.inv_hom_id_assoc]

/-- **The limit `X` of the product situation is the base change `X_{c.pt}`.** -/
noncomputable def productSourceLimitIso :
    (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceLimitSpace ≅
      productSpace X₀ c.pt :=
  ObjectProperty.isoMk _
    (pullbackProdFstIsoProd (limit.π (T ⋙ yoneda) (op j₀)) X₀.1 ≪≫
      prod.mapIso (productLimitIso T hc).symm (Iso.refl _))

/-- The identification `productSourceLimitIso` of the limit `X` with `X_{c.pt}` is compatible with
the maps to `X_{T j₀}`. -/
theorem productSourceLimitIso_hom_comp :
    (productSourceLimitIso hZ T hc X₀ j₀ hqc hqs).hom ≫
        productSpaceMap X₀ (V := c.pt) (c.π.app (op j₀)) =
      (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceLimitToSource₀ := by
  apply ObjectProperty.hom_ext
  change ((pullbackProdFstIsoProd (limit.π (T ⋙ yoneda) (op j₀)) X₀.1).hom ≫
      prod.map (productLimitIso T hc).inv (𝟙 X₀.1)) ≫
        prod.map (yoneda.map (c.π.app (op j₀))) (𝟙 X₀.1) =
      pullback.snd (limit.π (T ⋙ yoneda) (op j₀))
        (prod.fst : yoneda.obj (T.obj (op j₀)) ⨯ X₀.1 ⟶ _)
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc, productLimitIso_inv_map,
      pullbackProdFstIsoProd_hom_fst_assoc]
    exact pullback.condition
  · simp

/-- The comparison `Y ⟶ h_{c.pt}` of the target at the limit of the product situation. -/
noncomputable def productTargetLimitHom :
    productTargetLimitSpace hZ T hc X₀ j₀ hqc hqs ⟶ schemeSpace c.pt :=
  ObjectProperty.homMk (show pullback (limit.π (T ⋙ yoneda) (op j₀))
      (𝟙 (yoneda.obj (T.obj (op j₀)))) ⟶ yoneda.obj c.pt from
    pullback.fst _ _ ≫ (productLimitIso T hc).inv)

/-- The comparison `productTargetLimitHom` is an isomorphism. -/
instance : IsIso (productTargetLimitHom hZ T hc X₀ j₀ hqc hqs) := by
  have h : IsIso ((ObjectProperty.ι _).map (productTargetLimitHom hZ T hc X₀ j₀ hqc hqs)) :=
    inferInstanceAs (IsIso (pullback.fst (limit.π (T ⋙ yoneda) (op j₀))
      (𝟙 (yoneda.obj (T.obj (op j₀)))) ≫ (productLimitIso T hc).inv))
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- The square comparing the limit of the product situation with the base change `X_{c.pt}`. -/
theorem isPullback_productSourceLimitIso :
    IsPullback (productSourceLimitIso hZ T hc X₀ j₀ hqc hqs).hom
      (ObjectProperty.homMk (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).mapLimit :
        (productMorphismDescentData hZ T hc X₀ j₀ hqc hqs).sourceLimitSpace ⟶
          productTargetLimitSpace hZ T hc X₀ j₀ hqc hqs)
      (productSpaceFst X₀ c.pt) (productTargetLimitHom hZ T hc X₀ j₀ hqc hqs) := by
  refine IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ ?_⟩
  dsimp only [productSourceLimitIso, productTargetLimitHom, productSpaceFst,
    MorphismDescentSituation.mapLimit, productMorphismDescentData,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.isoMk_hom, Iso.trans_hom, prod.mapIso_hom, Iso.symm_hom, Iso.refl_hom,
    ObjectProperty.homMk, ObjectProperty.isoMk]
  exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (prod.map_fst (productLimitIso T hc).inv (𝟙 X₀.1))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (productLimitIso T hc).inv)
          (pullbackProdFstIsoProd_hom_fst (limit.π (T ⋙ yoneda) (op j₀)) X₀.1))))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (productLimitIso T hc).inv) (pullback.lift_fst _ _ _))).symm

/-- The inverse image of the support of a pullback of `G` along `e` is the support of the pullback
along the composite. -/
private theorem preimage_supportOfSheaf_modulePullback_eq {A A' X : AlgebraicSpaces B S hS}
    (e : A ⟶ A') (g : A' ⟶ X) (h : A ⟶ X) (he : e ≫ g = h) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G) :
    pointsMap B S hS _ e.hom ⁻¹' supportOfSheaf B S hS A'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj G)) =
      supportOfSheaf B S hS A.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS h).obj G)) := by
  subst he
  rw [supportOfSheaf_modulePullback_eq B S hS g G hG hGft,
    preimage_pointsMap_preimage_pointsMap, supportOfSheaf_modulePullback_eq B S hS _ G hG hGft]
  rfl

include hZ hc hcS hqc hqs in
/-- **Stacks 08K2 for a base change along a limit of affine schemes.** Let `T` be a directed
inverse system of affine schemes over `S` whose limit `c.pt` is in the site, `X₀` an algebraic
space over `S` such that `X_{T j₀} = h_{T j₀} ⨯ X₀` is quasi-compact and quasi-separated and
locally of finite type over `T j₀`, and `G` a quasi-coherent `𝒪`-module of finite type on
`X_{T j₀}`. If the pullback of `G` to `X_{c.pt}` has support proper over `c.pt`, then for some
`j ≥ j₀` the pullback of `G` to `X_{T j}` has support proper over `T j`. -/
theorem exists_hasProperSupport_productSpaceMap
    (hlft : IsLocallyOfFiniteType B S hS (productSpaceFst X₀ (T.obj (op j₀))).hom)
    (G : Modules.{u, u} B S hS (productSpace X₀ (T.obj (op j₀))).1
      (productSpace X₀ (T.obj (op j₀))).2)
    (hG : G.IsQuasicoherentOnSite) (hGft : SheafOfModules.IsFiniteTypeOnSite G)
    (hlftL : IsLocallyOfFiniteType B S hS (productSpaceFst X₀ c.pt).hom)
    (hprop : HasProperSupport B S hS (productSpace X₀ c.pt).2 (schemeSpace c.pt).2
      (productSpaceFst X₀ c.pt).hom hlftL ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS (productSpaceMap X₀ (V := c.pt) (c.π.app (op j₀)))).obj G))) :
    ∃ (j : J) (h : j₀ ≤ j)
      (hlftj : IsLocallyOfFiniteType B S hS (productSpaceFst X₀ (T.obj (op j))).hom),
      HasProperSupport B S hS (productSpace X₀ (T.obj (op j))).2
        (schemeSpace (T.obj (op j))).2 (productSpaceFst X₀ (T.obj (op j))).hom hlftj
        ((SheafOfModules.toSheaf _).obj
          ((modulePullback B S hS (productSpaceMap X₀ (T.map (homOfLE h).op))).obj G)) := by
  set D := productMorphismDescentData hZ T hc X₀ j₀ hqc hqs
  have hf₀ : IsLocallyOfFiniteType B S hS D.map₀ := hlft
  have hsupp₀ := supportOfSheaf_modulePullback_eq B S hS
    (productSpaceMap X₀ (V := c.pt) (c.π.app (op j₀))) G hG hGft
  obtain ⟨hcl, hP⟩ := hprop
  have hlim := isProperOver_preimage B S hS (isPullback_productSourceLimitIso hZ T hc X₀ j₀
    hqc hqs) hlftL _ hcl hP
  have hsuppL := preimage_supportOfSheaf_modulePullback_eq
    (productSourceLimitIso hZ T hc X₀ j₀ hqc hqs).hom
    (productSpaceMap X₀ (V := c.pt) (c.π.app (op j₀))) D.sourceLimitToSource₀
    (productSourceLimitIso_hom_comp hZ T hc X₀ j₀ hqc hqs) G hG hGft
  obtain ⟨i, hi, hiP⟩ :=
    D.exists_isProperOver_supportOfSheaf_moduleAt_of_siteContainsBaseChangeLimits
      G (siteContainsBaseChangeLimits_productMorphismDescentData hZ T hc hcS X₀ j₀ hqc hqs) hG hf₀
      hGft (IsProperOver.of_eq hsuppL (D.isClosed_supportOfSheaf_moduleLimit G hGft) hlim)
  have hstage := isProperOver_preimage B S hS (isPullback_productSourceAtIso hZ T hc X₀ j₀
    hqc hqs i hi) (D.isLocallyOfFiniteType_mapAt hf₀ i hi) _ _ hiP
  have hsuppS := preimage_supportOfSheaf_modulePullback_eq
    (productSourceAtIso hZ T hc X₀ j₀ hqc hqs i hi).hom
    (D.sourceAtToSource₀ i hi) (productSpaceMap X₀ (T.map (homOfLE hi).op))
    (productSourceAtIso_hom_comp hZ T hc X₀ j₀ hqc hqs i hi) G hG hGft
  have hcl' := isClosed_supportOfSheaf_modulePullback B S hS
    (productSpaceMap X₀ (T.map (homOfLE hi).op)) G hGft
  exact ⟨i, hi, _, hcl', IsProperOver.of_eq hsuppS hcl' hstage⟩

end AlgebraicGeometry.Space

end

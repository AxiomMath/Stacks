module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Morphisms of modules along a limit of base changes of an algebraic space

Let `X₀` be an algebraic space over `S` and `T : I ⥤ (Sch/S)` a cofiltered system of affine
schemes whose underlying schemes have a limit `c`. For quasi-coherent modules `𝒢`, `ℋ` of finite
presentation on a quasi-compact base change `Y₀ = h_{T i₀} ⨯ X₀`, two morphisms `𝒢 ⟶ ℋ` whose
inverse images to `h_{c.pt} ⨯ X₀` agree have equal inverse images to some `h_{T j} ⨯ X₀`; if
`Y₀` is moreover quasi-separated, a morphism between the inverse images to `h_{c.pt} ⨯ X₀` is,
at some stage `j`, the inverse image of a morphism between the inverse images to
`h_{T j} ⨯ X₀`. These are the morphism clauses of Stacks 07V7 for the limit situation
`h_{T j} ⨯ X₀`.

## Main results

* `AlgebraicGeometry.Space.exists_productSpaceMap_map_eq_of_isLimit`: the faithfulness clause.
* `AlgebraicGeometry.Space.exists_homTransport_productSpaceMap_eq_of_isLimit`: the fullness
  clause.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)
  {I : Type u} [Category.{u} I] (T : I ⥤ BigFppfOver B S hS) (i₀ : I)
  {U₀ : BigFppfOver B S hS} (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ (T.obj i₀)).1)

/-! ### The charts as morphisms of algebraic spaces -/

/-- The chart `U₀ ×_{T i₀} T j ⟶ h_{T j} ⨯ X₀`, as a morphism of algebraic spaces. -/
noncomputable def productChartSpaceMap (k : Over i₀) :
    schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k) ⟶ productSpace X₀ (T.obj k.left) :=
  ObjectProperty.homMk (productChartMap X₀ a₀ (T.map k.hom))

/-- The composite `U₀ ×_{T i₀} T j ⟶ U₀ ⟶ h_{T i₀} ⨯ X₀`. -/
noncomputable def productChartSpaceBase (k : Over i₀) :
    schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k) ⟶ productSpace X₀ (T.obj i₀) :=
  ObjectProperty.homMk (yoneda.map (pullback.fst (productChartBase X₀ a₀) (T.map k.hom)) ≫ a₀)

/-- The chart of a stage followed by the transition map `h_{T j} ⨯ X₀ ⟶ h_{T i₀} ⨯ X₀` is
`AlgebraicGeometry.Space.productChartSpaceBase`. -/
theorem productChartSpaceMap_comp (k : Over i₀) :
    productChartSpaceMap X₀ T i₀ a₀ k ≫ productSpaceMap X₀ (V' := T.obj i₀) (T.map k.hom) =
      productChartSpaceBase X₀ T i₀ a₀ k :=
  ObjectProperty.hom_ext _ (productChartMap_comp_productSpaceMap_self X₀ a₀ (T.map k.hom))

/-- The transition maps of the charts commute with the composites to `h_{T i₀} ⨯ X₀`. -/
theorem schemeSpaceMap_comp_productChartSpaceBase {k k' : Over i₀} (f : k ⟶ k') :
    schemeSpaceMap ((productChartSystem X₀ T i₀ a₀).map f) ≫ productChartSpaceBase X₀ T i₀ a₀ k' =
      productChartSpaceBase X₀ T i₀ a₀ k :=
  ObjectProperty.hom_ext _ ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ a₀) ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (productChartSystem_map_fst X₀ T i₀ a₀ f)))))

/-- The chart `U₀ ×_{T i₀} T j ⟶ h_{T j} ⨯ X₀` is étale. -/
theorem isEtale_productChartSpaceMap
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀) (k : Over i₀) :
    IsEtale B S hS (productChartSpaceMap X₀ T i₀ a₀ k).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).2 (productChartMap_etale X₀ ha₀ (T.map k.hom))

/-- The chart `U₀ ×_{T i₀} T j ⟶ h_{T j} ⨯ X₀` is an étale covering. -/
theorem isEtaleCovering_productChartSpaceMap
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀) (k : Over i₀) :
    IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k)).1)
      (fun _ => (productChartSpaceMap X₀ T i₀ a₀ k).hom) :=
  isEtaleCovering_atlas B S hS (productSpace X₀ (T.obj k.left)).2
    (productChartMap_surjective X₀ hs₀ (T.map k.hom)) (productChartMap_etale X₀ ha₀ (T.map k.hom))

variable (c : Cone T)

/-- The projection of the base change to the cone point to the base change to a stage. -/
noncomputable abbrev productSpaceConeMap (k : I) :
    productSpace X₀ c.pt ⟶ productSpace X₀ (T.obj k) :=
  productSpaceMap X₀ (V := c.pt) (c.π.app k)

/-- The projection of the chart of the cone point to the chart of a stage. -/
noncomputable abbrev productChartConeπ (k : Over i₀) :
    schemeSpace (productChartCone X₀ T i₀ a₀ c).pt ⟶
      schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k) :=
  schemeSpaceMap (U := (productChartCone X₀ T i₀ a₀ c).pt) ((productChartCone X₀ T i₀ a₀ c).π.app k)

/-- The chart `U₀ ×_{T i₀} c.pt ⟶ h_{c.pt} ⨯ X₀`, as a morphism of algebraic spaces. -/
noncomputable def productChartConeSpaceMap :
    schemeSpace (productChartCone X₀ T i₀ a₀ c).pt ⟶ productSpace X₀ c.pt :=
  ObjectProperty.homMk (productChartMap X₀ a₀ (V := c.pt) (c.π.app i₀))

/-- The composite `U₀ ×_{T i₀} c.pt ⟶ U₀ ⟶ h_{T i₀} ⨯ X₀`. -/
noncomputable def productChartConeSpaceBase :
    schemeSpace (productChartCone X₀ T i₀ a₀ c).pt ⟶ productSpace X₀ (T.obj i₀) :=
  ObjectProperty.homMk (yoneda.map (pullback.fst (productChartBase X₀ a₀) (c.π.app i₀)) ≫ a₀)

/-- The chart of the cone point followed by the projection `h_{c.pt} ⨯ X₀ ⟶ h_{T i₀} ⨯ X₀` is
`AlgebraicGeometry.Space.productChartConeSpaceBase`. -/
theorem productChartConeSpaceMap_comp :
    productChartConeSpaceMap X₀ T i₀ a₀ c ≫ productSpaceConeMap X₀ T c i₀ =
      productChartConeSpaceBase X₀ T i₀ a₀ c :=
  ObjectProperty.hom_ext _ (productChartMap_comp_productSpaceMap_self X₀ a₀
    (V := c.pt) (c.π.app i₀))

/-- The chart `U₀ ×_{T i₀} c.pt ⟶ h_{c.pt} ⨯ X₀` is an étale covering. -/
theorem isEtaleCovering_productChartConeSpaceMap
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀) :
    IsEtaleCovering B S hS (fun _ : Unit => (schemeSpace (productChartCone X₀ T i₀ a₀ c).pt).1)
      (fun _ => (productChartConeSpaceMap X₀ T i₀ a₀ c).hom) :=
  isEtaleCovering_atlas B S hS (productSpace X₀ c.pt).2
    (productChartMap_surjective X₀ hs₀ (V := c.pt) (c.π.app i₀))
    (productChartMap_etale X₀ ha₀ (V := c.pt) (c.π.app i₀))

/-- The projections of the chart of the cone point commute with the composites to
`h_{T i₀} ⨯ X₀`. -/
theorem schemeSpaceMap_comp_productChartSpaceBase_cone (k : Over i₀) :
    productChartConeπ X₀ T i₀ a₀ c k ≫ productChartSpaceBase X₀ T i₀ a₀ k =
      productChartConeSpaceBase X₀ T i₀ a₀ c :=
  ObjectProperty.hom_ext _ ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ a₀) ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (productChartCone_π_app_fst X₀ T i₀ a₀ c k)))))

/-- The chart of the limit lies over the chart of a stage. -/
theorem productChartConeSpaceMap_comp_productSpaceMap (k : Over i₀) :
    productChartConeSpaceMap X₀ T i₀ a₀ c ≫
        productSpaceConeMap X₀ T c k.left =
      productChartConeπ X₀ T i₀ a₀ c k ≫
        productChartSpaceMap X₀ T i₀ a₀ k :=
  ObjectProperty.hom_ext _ (productChartMap_comp_productSpaceMap X₀ a₀ (T.map k.hom)
    (c.π.app i₀) (c.π.app k.left) (c.w k.hom))

/-- The projection to the stage `j` followed by the transition map along `e : j ⟶ i₀` is the
projection to the stage `i₀`. -/
theorem productSpaceConeMap_comp {j : I} (e : j ⟶ i₀) :
    productSpaceConeMap X₀ T c j ≫ productSpaceMap X₀ (T.map e) =
      productSpaceConeMap X₀ T c i₀ := by
  rw [productSpaceConeMap, productSpaceConeMap, ← productSpaceMap_comp, c.w]

/-- The projection to the stage `k.left` followed by the transition map along `k.hom` is the
projection to the stage `i₀`. -/
theorem productSpaceMap_cone_comp (k : Over i₀) :
    productSpaceConeMap X₀ T c k.left ≫ productSpaceMap X₀ (V' := T.obj i₀) (T.map k.hom) =
      productSpaceConeMap X₀ T c i₀ := by
  rw [productSpaceConeMap, productSpaceConeMap, ← productSpaceMap_comp, c.w]

/-! ### Morphisms of charts -/

section PairMap

variable {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
  (a₁ : yoneda.obj R₀ ⟶ (productSpace X₀ (T.obj i₀)).1) (hg : yoneda.map g ≫ a₀ = a₁)

/-- The morphism of charts `R₀ ×_{T i₀} T j ⟶ U₀ ×_{T i₀} T j` induced by `g : R₀ ⟶ U₀`. -/
noncomputable def productChartSpacePairMap (k : Over i₀) :
    schemeSpace ((productChartSystem X₀ T i₀ a₁).obj k) ⟶
      schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k) :=
  schemeSpaceMap (productChartPairMap X₀ a₀ g a₁ hg (T.map k.hom))

/-- The morphism of charts induced by `g` commutes with the composites to `h_{T i₀} ⨯ X₀`. -/
theorem productChartSpacePairMap_comp_base (k : Over i₀) :
    productChartSpacePairMap X₀ T i₀ a₀ g a₁ hg k ≫ productChartSpaceBase X₀ T i₀ a₀ k =
      productChartSpaceBase X₀ T i₀ a₁ k :=
  ObjectProperty.hom_ext _ <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ a₀) ((yoneda.map_comp _ _).symm.trans
      (congrArg yoneda.map (productChartPairMap_fst X₀ a₀ g a₁ hg (T.map k.hom))))).trans <|
    (congrArg (· ≫ a₀) (yoneda.map_comp _ _)).trans <|
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hg)

/-- The morphism of charts induced by `g` commutes with the charts to `h_{T j} ⨯ X₀`. -/
theorem productChartSpacePairMap_comp_chart (k : Over i₀) :
    productChartSpacePairMap X₀ T i₀ a₀ g a₁ hg k ≫ productChartSpaceMap X₀ T i₀ a₀ k =
      productChartSpaceMap X₀ T i₀ a₁ k :=
  ObjectProperty.hom_ext _ (yoneda_map_productChartPairMap X₀ a₀ g a₁ hg (T.map k.hom))

/-- The morphisms of charts induced by `g` commute with the transition maps of the charts. -/
theorem productChartSystem_map_comp_productChartPairMap {k k' : Over i₀} (f : k ⟶ k') :
    (productChartSystem X₀ T i₀ a₁).map f ≫ productChartPairMap X₀ a₀ g a₁ hg (T.map k'.hom) =
      productChartPairMap X₀ a₀ g a₁ hg (T.map k.hom) ≫ (productChartSystem X₀ T i₀ a₀).map f :=
  pullback.hom_ext
    (((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartPairMap_fst X₀ a₀ g a₁ hg _)).trans <|
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (productChartSystem_map_fst X₀ T i₀ a₁ f))).trans
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (productChartSystem_map_fst X₀ T i₀ a₀ f)).trans
          (productChartPairMap_fst X₀ a₀ g a₁ hg _)).symm)
    (((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartPairMap_snd X₀ a₀ g a₁ hg _)).trans
        (productChartSystem_map_snd X₀ T i₀ a₁ f)).trans
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (productChartSystem_map_snd X₀ T i₀ a₀ f)).trans <|
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (productChartPairMap_snd X₀ a₀ g a₁ hg _))).symm)

/-- The morphisms of charts induced by `g`, as morphisms of algebraic spaces, commute with the
transition maps of the charts. -/
theorem schemeSpaceMap_comp_productChartSpacePairMap {k k' : Over i₀} (f : k ⟶ k') :
    schemeSpaceMap ((productChartSystem X₀ T i₀ a₁).map f) ≫
        productChartSpacePairMap X₀ T i₀ a₀ g a₁ hg k' =
      productChartSpacePairMap X₀ T i₀ a₀ g a₁ hg k ≫
        schemeSpaceMap ((productChartSystem X₀ T i₀ a₀).map f) :=
  ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    ((congrArg yoneda.map
      (productChartSystem_map_comp_productChartPairMap X₀ T i₀ a₀ g a₁ hg f)).trans
      (yoneda.map_comp _ _)))

/-- **The kernel pair of the chart of a stage**, from a kernel pair of `a₀`. -/
theorem isPullback_productChartSpacePairMap {s₀ t₀ : R₀ ⟶ U₀}
    (hk : IsPullback (yoneda.map s₀) (yoneda.map t₀) a₀ a₀) (hs : yoneda.map s₀ ≫ a₀ = a₁)
    (ht : yoneda.map t₀ ≫ a₀ = a₁) (k : Over i₀) :
    IsPullback (productChartSpacePairMap X₀ T i₀ a₀ s₀ a₁ hs k).hom
      (productChartSpacePairMap X₀ T i₀ a₀ t₀ a₁ ht k).hom
      (productChartSpaceMap X₀ T i₀ a₀ k).hom (productChartSpaceMap X₀ T i₀ a₀ k).hom :=
  isPullback_productChartKernelPair X₀ a₀ hk a₁ hs ht (T.map k.hom)

variable (c : Cone T)

/-- The morphism of the charts of the cone point induced by `g`. -/
noncomputable def productChartConeSpacePairMap :
    schemeSpace (productChartCone X₀ T i₀ a₁ c).pt ⟶
      schemeSpace (productChartCone X₀ T i₀ a₀ c).pt :=
  schemeSpaceMap (productChartPairMap X₀ a₀ g a₁ hg (c.π.app i₀))

/-- The morphism of the charts of the cone point induced by `g` commutes with the charts to
`h_{c.pt} ⨯ X₀`. -/
theorem productChartConeSpacePairMap_comp_chart :
    productChartConeSpacePairMap X₀ T i₀ a₀ g a₁ hg c ≫ productChartConeSpaceMap X₀ T i₀ a₀ c =
      productChartConeSpaceMap X₀ T i₀ a₁ c :=
  ObjectProperty.hom_ext _ (yoneda_map_productChartPairMap X₀ a₀ g a₁ hg (V := c.pt) (c.π.app i₀))

/-- The morphisms of charts induced by `g` commute with the projections from the charts of the cone
point. -/
theorem productChartCone_π_app_comp_productChartPairMap (k : Over i₀) :
    (productChartCone X₀ T i₀ a₁ c).π.app k ≫ productChartPairMap X₀ a₀ g a₁ hg (T.map k.hom) =
      productChartPairMap X₀ a₀ g a₁ hg (c.π.app i₀) ≫ (productChartCone X₀ T i₀ a₀ c).π.app k :=
  pullback.hom_ext
    (((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartPairMap_fst X₀ a₀ g a₁ hg _)).trans <|
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (productChartCone_π_app_fst X₀ T i₀ a₁ c k))).trans
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (productChartCone_π_app_fst X₀ T i₀ a₀ c k)).trans
          (productChartPairMap_fst X₀ a₀ g a₁ hg _)).symm)
    (((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartPairMap_snd X₀ a₀ g a₁ hg _)).trans
        (productChartCone_π_app_snd X₀ T i₀ a₁ c k)).trans
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (productChartCone_π_app_snd X₀ T i₀ a₀ c k)).trans <|
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (productChartPairMap_snd X₀ a₀ g a₁ hg _))).symm)

/-- The morphisms of charts induced by `g`, as morphisms of algebraic spaces, commute with the
projections from the charts of the cone point. -/
theorem productChartConeπ_comp_productChartSpacePairMap (k : Over i₀) :
    productChartConeπ X₀ T i₀ a₁ c k ≫ productChartSpacePairMap X₀ T i₀ a₀ g a₁ hg k =
      productChartConeSpacePairMap X₀ T i₀ a₀ g a₁ hg c ≫ productChartConeπ X₀ T i₀ a₀ c k :=
  ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    ((congrArg yoneda.map
      (productChartCone_π_app_comp_productChartPairMap X₀ T i₀ a₀ g a₁ hg c k)).trans
      (yoneda.map_comp _ _)))

end PairMap

/-! ### Faithfulness -/

/-- **Morphisms of modules agreeing on the limit of base changes agree at a stage** (the
faithfulness clause of Stacks 07V7, for the limit situation `h_{T j} ⨯ X₀`). -/
theorem exists_productSpaceMap_map_eq_of_isLimit [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj i₀)).1)
    {G H : Modules.{u, u} B S hS (productSpace X₀ (T.obj i₀)).1 (productSpace X₀ (T.obj i₀)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite) (ψ₁ ψ₂ : G ⟶ H)
    (h : (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).map ψ₁ =
      (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i₀), (modulePullback B S hS (productSpaceMap X₀ (T.map e))).map ψ₁ =
      (modulePullback B S hS (productSpaceMap X₀ (T.map e))).map ψ₂ := by
  obtain ⟨U₀, a₀, hU₀, hs₀, ha₀'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
      (productSpace X₀ (T.obj i₀)).2).mp hqc
  have ha₀ := (isEtale_iff_presheaf_of_yoneda B S hS a₀).mp ha₀'
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((productChartSystem X₀ T i₀ a₀).obj (Over.mk (𝟙 i₀)))) :=
    Scheme.compactSpace_of_isAffine _
  have hlim : (modulePullback B S hS
        (productChartConeπ X₀ T i₀ a₀ c (Over.mk (𝟙 i₀)))).map
        ((modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ (Over.mk (𝟙 i₀)))).map ψ₁) =
      (modulePullback B S hS
        (productChartConeπ X₀ T i₀ a₀ c (Over.mk (𝟙 i₀)))).map
        ((modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ (Over.mk (𝟙 i₀)))).map ψ₂) := by
    rw [map_map_eq_iff _ _ (schemeSpaceMap_comp_productChartSpaceBase_cone X₀ T i₀ a₀ c _),
      ← productChartConeSpaceMap_comp X₀ T i₀ a₀ c,
      ← map_map_eq_iff _ _ rfl, h]
  obtain ⟨k, f, hk⟩ := exists_modulePullback_map_eq_of_isLimit B S hS
    (productChartSystem X₀ T i₀ a₀) (productChartCone X₀ T i₀ a₀ c)
    (isLimitProductChartCone X₀ T i₀ a₀ c hc) (Over.mk (𝟙 i₀))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)
    (isFinitePresentationOnSite_modulePullback B S hS _ G hGfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ H hH)
    (isFinitePresentationOnSite_modulePullback B S hS _ H hHfp)
    ((modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ (Over.mk (𝟙 i₀)))).map ψ₁)
    ((modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ (Over.mk (𝟙 i₀)))).map ψ₂)
    (by dsimp only [Functor.const_obj_obj]; exact hlim)
  have hk' : (modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ k)).map ψ₁ =
      (modulePullback B S hS (productChartSpaceBase X₀ T i₀ a₀ k)).map ψ₂ := by
    rwa [map_map_eq_iff _ _ (schemeSpaceMap_comp_productChartSpaceBase X₀ T i₀ a₀ f)] at hk
  refine ⟨k.left, k.hom, modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : Unit => schemeSpace ((productChartSystem X₀ T i₀ a₀).obj k))
    (fun _ => productChartSpaceMap X₀ T i₀ a₀ k)
    (isEtaleCovering_productChartSpaceMap X₀ T i₀ a₀ ha₀ hs₀ k) _ _ fun _ => ?_⟩
  rwa [map_map_eq_iff _ _ (productChartSpaceMap_comp X₀ T i₀ a₀ k)]

/-! ### Fullness -/

/-- **A morphism of inverse images to the limit of base changes descends to a stage**, given an
affine étale surjective chart `a₀` of `h_{T i₀} ⨯ X₀` with a quasi-compact kernel pair. -/
theorem exists_homTransport_productSpaceMap_eq_of_kernelPair [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    (ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a₀)
    {R₀ : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj R₀)]
    {s₀ t₀ : R₀ ⟶ U₀} (hk : IsPullback (yoneda.map s₀) (yoneda.map t₀) a₀ a₀)
    (a₁ : yoneda.obj R₀ ⟶ (productSpace X₀ (T.obj i₀)).1) (hs : yoneda.map s₀ ≫ a₀ = a₁)
    (ht : yoneda.map t₀ ≫ a₀ = a₁)
    {G H : Modules.{u, u} B S hS (productSpace X₀ (T.obj i₀)).1 (productSpace X₀ (T.obj i₀)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).obj G ⟶
      (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).obj H) :
    ∃ (k : Over i₀) (χ : (modulePullback B S hS
        (productSpaceMap X₀ (V' := T.obj i₀) (T.map k.hom))).obj G ⟶
        (modulePullback B S hS (productSpaceMap X₀ (V' := T.obj i₀) (T.map k.hom))).obj H),
      homTransport G H (productSpaceConeMap X₀ T c k.left) (productSpaceMap_cone_comp X₀ T i₀ c k)
        χ = φ :=
  exists_homTransport_eq_of_charts (Y := fun k : Over i₀ => productSpace X₀ (T.obj k.left))
    (fun k => productSpaceMap X₀ (V' := T.obj i₀) (T.map k.hom))
    (fun k => productSpaceConeMap X₀ T c k.left) (productSpaceMap_cone_comp X₀ T i₀ c)
    (productChartCone X₀ T i₀ a₀ c) (isLimitProductChartCone X₀ T i₀ a₀ c hc)
    (productChartSpaceMap X₀ T i₀ a₀) (productChartConeSpaceMap X₀ T i₀ a₀ c)
    (fun f => by
      rw [productChartSpaceMap_comp, productChartSpaceMap_comp,
        schemeSpaceMap_comp_productChartSpaceBase])
    (productChartConeSpaceMap_comp_productSpaceMap X₀ T i₀ a₀ c)
    (isEtale_productChartSpaceMap X₀ T i₀ a₀ ha₀)
    (isEtaleCovering_productChartSpaceMap X₀ T i₀ a₀ ha₀ hs₀)
    (isEtaleCovering_productChartConeSpaceMap X₀ T i₀ a₀ c ha₀ hs₀)
    (productChartCone X₀ T i₀ a₁ c) (isLimitProductChartCone X₀ T i₀ a₁ c hc)
    (productChartSpacePairMap X₀ T i₀ a₀ s₀ a₁ hs) (productChartSpacePairMap X₀ T i₀ a₀ t₀ a₁ ht)
    (productChartConeSpacePairMap X₀ T i₀ a₀ s₀ a₁ hs c)
    (productChartConeSpacePairMap X₀ T i₀ a₀ t₀ a₁ ht c)
    (schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ a₀ s₀ a₁ hs)
    (schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ a₀ t₀ a₁ ht)
    (productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ a₀ s₀ a₁ hs c)
    (productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ a₀ t₀ a₁ ht c)
    ((productChartConeSpacePairMap_comp_chart X₀ T i₀ a₀ s₀ a₁ hs c).trans
      (productChartConeSpacePairMap_comp_chart X₀ T i₀ a₀ t₀ a₁ ht c).symm)
    (isPullback_productChartSpacePairMap X₀ T i₀ a₀ a₁ hk hs ht) hG hGfp hH hHfp φ

/-- **A morphism of inverse images to the limit of base changes descends to a stage** (the
fullness clause of Stacks 07V7, for the limit situation `h_{T j} ⨯ X₀` with `h_{T i₀} ⨯ X₀`
quasi-compact and quasi-separated): a morphism `φ` between the inverse images to
`h_{c.pt} ⨯ X₀` of two quasi-coherent modules of finite presentation on `h_{T i₀} ⨯ X₀` is, for
some `e : j ⟶ i₀`, the inverse image of a morphism between their inverse images to
`h_{T j} ⨯ X₀`. -/
theorem exists_homTransport_productSpaceMap_eq_of_isLimit [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj i₀)).1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (productSpace X₀ (T.obj i₀)).1)
    {G H : Modules.{u, u} B S hS (productSpace X₀ (T.obj i₀)).1 (productSpace X₀ (T.obj i₀)).2}
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite)
    (hH : H.IsQuasicoherentOnSite) (hHfp : H.IsFinitePresentationOnSite)
    (φ : (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).obj G ⟶
      (modulePullback B S hS (productSpaceConeMap X₀ T c i₀)).obj H) :
    ∃ (j : I) (e : j ⟶ i₀) (ψ : (modulePullback B S hS (productSpaceMap X₀ (T.map e))).obj G ⟶
        (modulePullback B S hS (productSpaceMap X₀ (T.map e))).obj H),
      homTransport G H (productSpaceConeMap X₀ T c j) (productSpaceConeMap_comp X₀ T i₀ c e) ψ =
        φ := by
  obtain ⟨U₀, a₀, hU₀, hs₀, ha₀'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
      (productSpace X₀ (T.obj i₀)).2).mp hqc
  have ha₀ := (isEtale_iff_presheaf_of_yoneda B S hS a₀).mp ha₀'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀
  obtain ⟨W, hW, ⟨eW⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ _
    (productSpace X₀ (T.obj i₀)).2).mp hqs U₀ U₀ a₀ a₀ hU₀ hU₀
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := hW
  have hk : IsPullback (yoneda.map (Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.fst a₀ a₀)))
      (yoneda.map (Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.snd a₀ a₀))) a₀ a₀ := by
    rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
    exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩
      eW rfl rfl
  obtain ⟨k, χ, hχ⟩ := exists_homTransport_productSpaceMap_eq_of_kernelPair X₀ T i₀ a₀ c hc ha₀ hs₀
    hk _ rfl hk.w.symm hG hGfp hH hHfp φ
  exact ⟨k.left, k.hom, χ, hχ⟩

end AlgebraicGeometry.Space

end

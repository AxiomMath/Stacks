module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- The category of elements of the lower-shriek extension `Λ_g F` of a presheaf `F` on the big
fppf site of `S`, mapped to Construction A of the category of elements of `F`: the backward
1-morphism of `CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`. -/
def relocalizeElementsChart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g (fibredCategory B S hS F)).val where
  toFunctor := (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).inv.functor
  w := (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).inv.w

/-- **Points of an algebraic-space chart are compatible with Construction A.** For a 1-morphism
`c` from the category of elements of a presheaf `F` over `S` to a category fibred in groupoids
`𝒳`, the bijection of points of Construction A carries the point of `𝒳` that `c` assigns to a
point `x` of `F` to the point of Construction A of `𝒳` that the chart by `Λ_g F` assigns to the
point of `Λ_g F` corresponding to `x`. -/
theorem changeBasePointsEquiv_spacePointMap (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (c : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) (x : Space.points B S hS F) :
    changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property (spacePointMap B S hS F 𝒳 c x) =
      spacePointMap B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (BasedFunctor.comp (relocalizeElementsChart B S S' hS hS' g F)
          (changeBaseHom B S S' hS hS' g
            (Bicategory.InducedBicategory.mkHom c : fibredCategory B S hS F ⟶ 𝒳)).hom)
        (Space.pointsRelocalize B S S' hS hS' g F x) := by
  induction x using Quot.inductionOn with
  | h p =>
    change changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property
        (spacePointMap B S hS F 𝒳 c (p.class B S hS F)) = _
    rw [Space.pointsRelocalize_class, spacePointMap_class, spacePointMap_class]
    exact (class_eq_class_iff_hasCommonExtension B S' hS' _ _ _ _).2 ⟨_, ⟨𝟙 _⟩, ⟨𝟙 _⟩⟩

/-- The chart of Construction A of `𝒳` by the algebraic space `Λ_g F` over `S'` attached to a
chart `c` of `𝒳` by an algebraic space `F` over `S`. -/
def changeBaseChart (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) :
    (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val :=
  BasedFunctor.comp (relocalizeElementsChart B S S' hS hS' g F)
    (changeBaseHom B S S' hS hS' g
      (Bicategory.InducedBicategory.mkHom c : fibredCategory B S hS F ⟶ 𝒳)).hom

/-- **The bijection of points of Construction A is continuous**: each chart of `𝒳` by an
algebraic space `F` corresponds to the chart of Construction A by `Λ_g F`
(`AlgebraicGeometry.Stack.changeBasePointsEquiv_spacePointMap`), and reading the points of `F`
over the larger base is continuous. -/
theorem continuous_changeBasePointsEquiv
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    @Continuous _ _ (pointTopology B S hS 𝒳)
      (pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳))
      (changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property) := by
  let := pointTopology B S hS 𝒳
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
  refine continuous_def.2 fun W' hW' => (isOpen_pointTopology_iff B S hS 𝒳 _).2 fun c => ?_
  have hc' := (isOpen_pointTopology_iff B S' hS'
    (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) W').1 hW'
    ⟨⟨_, isAlgebraicSpace_viewOver B S S' hS hS' g c.1.1 c.1.2⟩,
      changeBaseChart B S S' hS hS' g 𝒳 c.1.1 c.2⟩
  convert (Space.continuous_pointsRelocalize B S S' hS hS' g c.1.1).isOpen_preimage _ hc'
    using 1
  ext x
  exact Iff.of_eq (congrArg (· ∈ W')
    (changeBasePointsEquiv_spacePointMap B S S' hS hS' g c.1.1 𝒳 c.2 x))

/-- The identity based functor of a category fibred in groupoids is an equivalence. -/
private theorem isEquivalence_basedFunctor_id
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence (𝟭 _))

/-- **A flat chart stays flat after Construction A.** Let `c` be a chart of a category fibred in
groupoids `𝒳` over `S` by an algebraic space `F`, representable by algebraic spaces and with flat
and locally of finitely presented represented base changes. Then the chart
`AlgebraicGeometry.Stack.changeBaseChart` of Construction A of `𝒳` by `Λ_g F` has flat and
locally of finitely presented represented base changes too: both properties are tested on every
étale chart, which Construction A does not change (Stacks 04X5), and the chart differs from
Construction A of `c` by an equivalence of sources. -/
theorem flat_lfp_changeBaseChart
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val)
    (hc : IsRepresentableByAlgebraicSpaces B S hS c)
    (hfl : ∀ (V : BigFppfOver B S hS) (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (fibredCategory B S hS F).val.p 𝒳.val.p y
          c.toFunctor)
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (Space.IsFlat B S hS (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom ∧
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom)) :
    ∀ (V : BigFppfOver B S' hS')
      (y : BigFppfOver B V.left.1 V.left.2 ⥤
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj)
      (_hy : y ⋙ (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom)
          (fibredCategory B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F)).val.p
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p y
          (changeBaseChart B S S' hS hS' g 𝒳 F c).toFunctor)
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (Space.IsFlat B S' hS' (algebraicSpaceMap B S' hS' V
          ((spacesOverSmallerBaseFunctor B V.left.1 S' V.left.2 hS' V.hom).obj ⟨G, hG⟩)).hom ∧
        Space.IsLocallyOfFinitePresentation B S' hS' (algebraicSpaceMap B S' hS' V
          ((spacesOverSmallerBaseFunctor B V.left.1 S' V.left.2 hS' V.hom).obj ⟨G, hG⟩)).hom) := by
  let ca : fibredCategory B S hS F ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom c
  have hreq : Functor.IsEquivalence (relocalizeElementsChart B S S' hS hS' g F).toFunctor :=
    (PresheafOfCategories.relocalizeElementsEquivalenceOver g F).toEquivalence.isEquivalence_inverse
  have hbeq := isEquivalence_basedFunctor_id B S' hS'
    (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
  have hflat := (hasRelativeProperty_smooth_changeBaseHom_iff B S S' hS hS' g
    (@AlgebraicGeometry.Flat.{u}) ca hc).2 (fun V y hy G hG hE => (hfl V y hy G hG hE).1)
  have hlfp := (hasRelativeProperty_smooth_changeBaseHom_iff B S S' hS hS' g
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) ca hc).2
    (fun V y hy G hG hE => (hfl V y hy G hG hE).2)
  exact relativeProperty_of_equivalences B S' hS'
    (fun _ _ k => Space.IsFlat B S' hS' k.hom ∧
      Space.IsLocallyOfFinitePresentation B S' hS' k.hom)
    (changeBaseChart B S S' hS hS' g 𝒳 F c) (changeBaseHom B S S' hS hS' g ca).hom
    (relocalizeElementsChart B S S' hS hS' g F) (BasedFunctor.id _) (Iso.refl _)
    (fun V y hy G hG hE => ⟨hflat V y hy G hG hE, hlfp V y hy G hG hE⟩)

/-- **The bijection of points of Construction A is open.** The scheme presentation of `𝒳`,
smooth and surjective, becomes after Construction A a chart by `Λ_g h_U` which is flat and locally
of finite presentation on every represented base change
(`AlgebraicGeometry.Stack.flat_lfp_comp_changeBase_of_smooth`), hence open on points (Stacks
04XL); the image of an open set of points of `𝒳` is the image under that chart of the
corresponding open set of points of `h_U`. -/
theorem isOpenMap_changeBasePointsEquiv
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    @IsOpenMap _ _ (pointTopology B S hS 𝒳)
      (pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳))
      (changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property) := by
  classical
  let := pointTopology B S hS 𝒳
  let := pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
  intro W hW
  obtain ⟨_hFib, -, -, U, fU, hfU, hAtlas⟩ := id h𝒳
  let hU := isAlgebraicSpace_yoneda B S hS U
  let Ucfg := schemeFibredCategory B S hS U
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let aU := representationMap B S hS (yoneda.obj U) Ucfg eU
  let fa : Ucfg ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom fU
  let Xalg : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨Ucfg, isAlgebraicStack_schemeFibredCategory B S hS U⟩
  let falg : Ualg ⟶ Xalg := Bicategory.InducedBicategory.mkHom fa
  have haeq : Functor.IsEquivalence aU.toFunctor := eU.symm.toEquivalence.isEquivalence_functor
  have haU : Function.Surjective (spacePointMap B S hS (yoneda.obj U) Ucfg aU) := by
    intro y
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_essSurj B S hS _ _ aU y
    obtain ⟨x, rfl⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U)).surjective z
    refine ⟨x, ?_⟩
    rw [← hz]
    induction x using Quot.inductionOn with
    | h p =>
      change spacePointMap B S hS (yoneda.obj U) Ucfg aU (p.class B S hS _) =
        pointsMap B S hS _ _ _ aU (spacePointMap B S hS (yoneda.obj U) _
          (BasedFunctor.id _) (p.class B S hS _))
      rw [spacePointMap_class, spacePointMap_class]
      rfl
  have hasurj : Function.Surjective (spacePointMap B S hS (yoneda.obj U) 𝒳 (aU.comp fU)) := by
    rw [spacePointMap_comp B S hS (yoneda.obj U) Ucfg 𝒳 aU fU]
    exact ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS falg hfU).2
      fun V y hy G hG hE => (hAtlas V y hy G hG hE).1).comp haU
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (aU.comp fU) :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS fU (aU.comp fU) aU
      (Iso.refl _)).1 hfU
  have hbeqX := isEquivalence_basedFunctor_id B S hS 𝒳
  have hfl := relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsFlat B S hS k.hom ∧ Space.IsLocallyOfFinitePresentation B S hS k.hom)
    (aU.comp fU) fU aU (BasedFunctor.id 𝒳.val) (Iso.refl _)
    (fun V y hy G hG hE => ⟨Space.isFlat_of_isSmooth B S hS _ (hAtlas V y hy G hG hE).2,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hAtlas V y hy G hG hE).2⟩)
  let c' := changeBaseChart B S S' hS hS' g 𝒳 (yoneda.obj U) (aU.comp fU)
  have hcomm :=
    changeBasePointsEquiv_spacePointMap B S S' hS hS' g (yoneda.obj U) 𝒳 (aU.comp fU)
  have hopen : @IsOpenMap _ _ (Space.pointTopology B S' hS' _)
      (pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳))
      (spacePointMap B S' hS' _ (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) c') :=
    isOpenMap_spacePointMap B S' hS' _
      (isAlgebraicSpace_viewOver B S S' hS hS' g _ hU)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      ((isAlgebraicStack_changeBase_iff B S S' hS hS' g 𝒳.val).2 h𝒳) c'
      (flat_lfp_changeBaseChart B S S' hS hS' g 𝒳 (yoneda.obj U) (aU.comp fU) hrep hfl)
  have himg : changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property '' W =
      spacePointMap B S' hS' _ (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳) c' ''
        (Space.pointsRelocalize B S S' hS hS' g (yoneda.obj U) ''
          (spacePointMap B S hS (yoneda.obj U) 𝒳 (aU.comp fU) ⁻¹' W)) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨x, rfl⟩ := hasurj w
      exact ⟨_, ⟨x, hw, rfl⟩, (hcomm x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, hx, hcomm x⟩
  have hset : @IsOpen _ (Space.pointTopology B S' hS' _)
      (Space.pointsRelocalize B S S' hS hS' g (yoneda.obj U) ''
        (spacePointMap B S hS (yoneda.obj U) 𝒳 (aU.comp fU) ⁻¹' W)) := by
    rw [Space.isOpen_pointsRelocalize_iff B S S' hS hS' g,
      Set.preimage_image_eq _ (Space.pointsRelocalize_injective B S S' hS hS' g _)]
    exact @Continuous.isOpen_preimage _ _ (Space.pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS 𝒳) _
      (continuous_spacePointMap B S hS (yoneda.obj U) hU 𝒳 (aU.comp fU)) _ hW
  convert hopen _ hset using 1
  exact himg

/-- **The topology of Stacks 04XL is unchanged by Construction A.** For an algebraic stack `𝒳`
over `S` and a morphism `g : S ⟶ S'` of the big fppf site, the bijection
`AlgebraicGeometry.Stack.changeBasePointsEquiv` between the points of `𝒳` and those of
Construction A of `𝒳` is a homeomorphism: it is continuous
(`AlgebraicGeometry.Stack.continuous_changeBasePointsEquiv`) and open
(`AlgebraicGeometry.Stack.isOpenMap_changeBasePointsEquiv`). -/
theorem isHomeomorph_changeBasePointsEquiv
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    @IsHomeomorph _ _ (pointTopology B S hS 𝒳)
      (pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳))
      (changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property) :=
  @IsHomeomorph.mk _ _ (pointTopology B S hS 𝒳)
    (pointTopology B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)) _
    (continuous_changeBasePointsEquiv B S S' hS hS' g 𝒳)
    (isOpenMap_changeBasePointsEquiv.{u, w} B S S' hS hS' g 𝒳 h𝒳)
    (changeBasePointsEquiv B S S' hS hS' g 𝒳.val 𝒳.property).bijective

end AlgebraicGeometry.Stack

end

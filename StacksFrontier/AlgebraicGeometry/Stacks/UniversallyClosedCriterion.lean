module

public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Maps.OpenSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation

/-!
# Universally closed representable 1-morphisms of algebraic stacks (Stacks 0512)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces. **Stacks 0512** says that `f` is universally closed — the relative property of Tag 04XB
at universal closedness of morphisms of algebraic spaces — exactly when, for every algebraic
stack `𝒵` over `𝒴`, the first projection of the canonical 2-fibre product `𝒵 ×_𝒴 𝒳` of Tag 04T2
is a closed map on points for the topology of Tag 04XL.

Both directions pass through the three transfers of
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedPoints` and through the chart of a
presentation, read not on the big fppf site of the presenting scheme but on the *slice* of the
ambient site over it (`AlgebraicGeometry.Stack.sliceChart`). That change of model is forced: the
presentation clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` charts an algebraic stack by
`AlgebraicGeometry.Stack.schemeFibredCategory`, whose objects are the slice of the ambient site,
while the relocalisation bridge `AlgebraicGeometry.Stack.representingMap_relocalizeFibre` — which
is what identifies the representing presheaf of a base change along a scheme-valued point — is
stated for `AlgebraicGeometry.Stack.schemeSlice`, whose objects are the big fppf site of that
scheme. The two are different categories fibred in groupoids, both represented by the presheaf
the scheme represents, and `AlgebraicGeometry.Stack.sliceChart` is the second read through the
first.

For the forward direction, universal closedness of `f` gives, at the scheme-valued point of `𝒴`
named by the chart, that the structural morphism of the lower-shriek extension of the presheaf
representing the base change is a closed morphism of algebraic spaces; the second transfer turns
that into closedness on points of the first projection of the canonical square over that point;
Tag 02XD's first-factor cancellation and the third transfer turn it into closedness of the first
projection of `U ×_𝒵 (𝒵 ×_𝒴 𝒳)`; and the open surjection `|U| → |𝒵|` descends it to `𝒵 ×_𝒴 𝒳`,
by `Topology.Maps.OpenSurjectiveDescent` with the surjectivity hypothesis supplied by Tag 04XH.

For the converse, a morphism `k : Z ⟶ h_U` of algebraic spaces is the morphism of representing
presheaves induced by a 1-morphism out of the category of elements of `Z` (Tag 04SW, onto); the
hypothesis at that algebraic stack, pushed through two first-factor cancellations, is closedness
on points of the first projection of `Z ×_U (U ×_𝒴 𝒳)`; the second transfer reads that on the
representing presheaves; and Tag 04SD identifies the representing presheaf of that apex with
`Z ×_{h_U} Λ_U T`, which is the base change `Space.UniversallyClosed` is asking about.

## Main definitions

* `AlgebraicGeometry.Stack.sliceChart`: a chart out of
  `AlgebraicGeometry.Stack.schemeFibredCategory`, read as a chart out of
  `AlgebraicGeometry.Stack.schemeSlice`.

## Main results

* `AlgebraicGeometry.Stack.exists_sliceChart_isOpenMap_surjective`: an algebraic stack has a
  chart by the slice of the site over a scheme which is open and surjective on points.
* `AlgebraicGeometry.Stack.representable_universallyClosed_iff_closedMap_baseChange`:
  **Stacks 0512**.

## Implementation notes

Stacks 04XC, 04XB and `AlgebraicGeometry.Stack.HasRelativeProperty` itself carry the instance
argument
`(Space.universallyClosedProperty B S hS).IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)`,
which is Stacks 041O (`AlgebraicGeometry.Space.universallyClosed_isLocalAtTarget_fpqc`, moved to
the fppf precoverage along Stacks 0DFQ). The route above does not need it: it instantiates the
definition of `AlgebraicGeometry.Stack.UniversallyClosed` directly and uses
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which needs only `RespectsIso`.

`AlgebraicGeometry.Stack.pointsMap_basedFunctorId`, from the file of Tag 04XL, is used directly.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart of an algebraic stack, read on the slice of the site.** The presentation clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` gives a chart out of
`AlgebraicGeometry.Stack.schemeFibredCategory B S hS U`; both that and
`AlgebraicGeometry.Stack.schemeSlice B S hS U` are represented by the presheaf `U` represents, and
this is the given chart read through the two representing equivalences as a chart out of the
latter. The bridge of Tag 04SW for a base change along a scheme-valued point is stated for the
latter model, which is why a consumer needs this. -/
noncomputable def sliceChart (U : BigFppfOver B S hS)
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (fU : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val) :
    (schemeSlice B S hS U).val ⥤ᵇ 𝒵.val :=
  (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
      (schemeSliceEquivalenceOver B S hS U)).inverse.comp
    ((representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)).functor.comp fU)

/-- `AlgebraicGeometry.Stack.sliceChart` and the given chart induce the same map on the points of
the representing presheaf: the two representing equivalences cancel, and 2-isomorphic 1-morphisms
induce the same map on points. -/
theorem pointsMap_sliceChart (U : BigFppfOver B S hS)
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (fU : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val) :
    pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
        (fibredCategory B S hS (yoneda.obj U)).property 𝒵.property
        ((representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
          (schemeSliceEquivalenceOver B S hS U)).functor.comp
            (sliceChart B S hS U 𝒵 fU)) =
      pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
        (fibredCategory B S hS (yoneda.obj U)).property 𝒵.property
        ((representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
          (PresheafOfCategories.sliceElementsEquivalenceOver U)).functor.comp fU) := by
  funext x
  have hu : pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property
      (fibredCategory B S hS (yoneda.obj U)).property
      ((representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
        (schemeSliceEquivalenceOver B S hS U)).functor.comp
      (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
        (schemeSliceEquivalenceOver B S hS U)).inverse) x = x :=
    (congrFun (pointsMap_eq_of_basedNatTrans B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property
      (fibredCategory B S hS (yoneda.obj U)).property
      (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
        (schemeSliceEquivalenceOver B S hS U)).unitIso.hom) x).trans
      (pointsMap_basedFunctorId B S hS (fibredCategory B S hS (yoneda.obj U)).property x)
  exact (pointsMap_comp B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property
      (fibredCategory B S hS (yoneda.obj U)).property 𝒵.property
      ((representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
        (schemeSliceEquivalenceOver B S hS U)).functor.comp
       (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
        (schemeSliceEquivalenceOver B S hS U)).inverse)
      ((representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)).functor.comp fU) x).symm.trans
    (congrArg (pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property 𝒵.property
      ((representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)).functor.comp fU)) hu)


/-- A homeomorphism can be cancelled from an open map. -/
private theorem isOpenMap_of_comp_isHomeomorph {A C D : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [TopologicalSpace D] {sigma : A → C} {q : C → D}
    (hs : IsHomeomorph sigma) (h : IsOpenMap (q ∘ sigma)) : IsOpenMap q := by
  intro W hW
  have himg : q '' W = (q ∘ sigma) '' (sigma ⁻¹' W) := by
    rw [Set.image_comp, Set.image_preimage_eq _ hs.bijective.surjective]
  rw [himg]
  exact h _ (hW.preimage hs.continuous)

/-- The chart of `AlgebraicGeometry.Stack.schemeSlice B S hS U` by the presheaf `U` represents.
Named so that the statements below mention it rather than its expansion. -/
noncomputable abbrev sliceRepChart (U : BigFppfOver B S hS) :
    (fibredCategory B S hS (yoneda.obj U)).val ⥤ᵇ (schemeSlice B S hS U).val :=
  (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
    (schemeSliceEquivalenceOver B S hS U)).functor

/-- The chart of `AlgebraicGeometry.Stack.schemeFibredCategory B S hS U` by the presheaf `U`
represents. Named so that the statements below mention it rather than its expansion. -/
noncomputable abbrev schemeRepChart (U : BigFppfOver B S hS) :
    (fibredCategory B S hS (yoneda.obj U)).val ⥤ᵇ (schemeFibredCategory B S hS U).val :=
  (representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)).functor

/-- `AlgebraicGeometry.Stack.pointsMap_sliceChart` read on the canonical map from the points of
the representing presheaf: the two charts of the algebraic stack induce the same map there. -/
theorem spacePointMap_sliceChart (U : BigFppfOver B S hS)
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (fU : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val) :
    spacePointMap B S hS (yoneda.obj U) 𝒵
        ((sliceRepChart B S hS U).comp (sliceChart B S hS U 𝒵 fU)) =
      spacePointMap B S hS (yoneda.obj U) 𝒵 ((schemeRepChart B S hS U).comp fU) := by
  have h1 := spacePointMap_comp B S hS (yoneda.obj U)
    (fibredCategory B S hS (yoneda.obj U)) 𝒵
    (BasedFunctor.id (fibredCategory B S hS (yoneda.obj U)).val)
    ((sliceRepChart B S hS U).comp (sliceChart B S hS U 𝒵 fU))
  have h2 := spacePointMap_comp B S hS (yoneda.obj U)
    (fibredCategory B S hS (yoneda.obj U)) 𝒵
    (BasedFunctor.id (fibredCategory B S hS (yoneda.obj U)).val)
    ((schemeRepChart B S hS U).comp fU)
  rw [BasedFunctor.id_comp] at h1 h2
  rw [h1, h2, pointsMap_sliceChart]



/-- **The slice chart of a presentation of an algebraic stack is open and surjective on points.**
An algebraic stack has, by the fourth clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`, a
smooth surjective chart by the big fppf site of a scheme `U`; read through
`AlgebraicGeometry.Stack.sliceChart` as a chart by the slice of the site over `U`, the map it
induces on points is surjective by Tag 04XI and open by the openness clause of Tag 04XL. -/
theorem exists_sliceChart_isOpenMap_surjective (𝒵 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (U : BigFppfOver B S hS) (c : (schemeSlice B S hS U).val ⥤ᵇ 𝒵.val.val),
      Function.Surjective (pointsMap B S hS (schemeSlice B S hS U).val
          (schemeSlice B S hS U).property 𝒵.val.property c) ∧
        @IsOpenMap _ _ (pointTopology B S hS (schemeSlice B S hS U))
          (pointTopology B S hS 𝒵.val)
          (pointsMap B S hS (schemeSlice B S hS U).val
            (schemeSlice B S hS U).property 𝒵.val.property c) := by
  classical
  have hcopy := 𝒵.property
  obtain ⟨_hFib, -, -, U, fU, hfU, hAtlas⟩ := hcopy
  have hU := isAlgebraicSpace_yoneda B S hS U
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeFibredCategory B S hS U, isAlgebraicStack_schemeFibredCategory B S hS U⟩
  let falg : Ualg ⟶ 𝒵 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom fU)
  have hsurjPts := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS falg hfU).2
    (fun V y hy G hG hE => (hAtlas V y hy G hG hE).1)
  have hsurjChart : Function.Surjective
      (spacePointMap B S hS (yoneda.obj U) 𝒵.val ((schemeRepChart B S hS U).comp fU)) := by
    rw [spacePointMap_comp B S hS (yoneda.obj U) (schemeFibredCategory B S hS U) 𝒵.val
      (schemeRepChart B S hS U) fU]
    exact hsurjPts.comp (bijective_spacePointMap_representing B S hS (yoneda.obj U)
      (schemeFibredCategory B S hS U)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)).surjective
  have haeq : Functor.IsEquivalence (schemeRepChart B S hS U).toFunctor :=
    ((StacksRepresentableCFG.EquivalenceOver.refl
      (fibredCategory B S hS (yoneda.obj U)).val.p).trans
      (PresheafOfCategories.sliceElementsEquivalenceOver U).symm).isEquivalence_hom_functor
  have hbeq : Functor.IsEquivalence (BasedFunctor.id 𝒵.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.val.val.obj))
  have hopenChart : @IsOpenMap _ _ (Space.pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS 𝒵.val)
      (spacePointMap B S hS (yoneda.obj U) 𝒵.val ((schemeRepChart B S hS U).comp fU)) := by
    refine isOpenMap_spacePointMap B S hS (yoneda.obj U) hU 𝒵.val 𝒵.property
      ((schemeRepChart B S hS U).comp fU) ?_
    refine relativeProperty_of_equivalences B S hS
      (fun _ _ k => Space.IsFlat B S hS k.hom ∧
        Space.IsLocallyOfFinitePresentation B S hS k.hom)
      ((schemeRepChart B S hS U).comp fU) fU (schemeRepChart B S hS U)
      (BasedFunctor.id 𝒵.val.val) (Iso.refl _) ?_
    intro V y hy G hG hE
    have hsm := (hAtlas V y hy G hG hE).2
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  have hfac : (pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
          𝒵.val.property (sliceChart B S hS U 𝒵.val fU)) ∘
        (spacePointMap B S hS (yoneda.obj U) (schemeSlice B S hS U)
          (sliceRepChart B S hS U)) =
      spacePointMap B S hS (yoneda.obj U) 𝒵.val ((schemeRepChart B S hS U).comp fU) :=
    (spacePointMap_comp B S hS (yoneda.obj U) (schemeSlice B S hS U) 𝒵.val
      (sliceRepChart B S hS U) (sliceChart B S hS U 𝒵.val fU)).symm.trans
      (spacePointMap_sliceChart B S hS U 𝒵.val fU)
  refine ⟨U, sliceChart B S hS U 𝒵.val fU, ?_, ?_⟩
  · intro z
    obtain ⟨a, ha⟩ := hsurjChart z
    exact ⟨spacePointMap B S hS (yoneda.obj U) (schemeSlice B S hS U)
      (sliceRepChart B S hS U) a, (congrFun hfac a).trans ha⟩
  · refine @isOpenMap_of_comp_isHomeomorph _ _ _
      (Space.pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS (schemeSlice B S hS U)) (pointTopology B S hS 𝒵.val) _ _
      (isHomeomorph_spacePointMap_representing B S hS (yoneda.obj U) hU
        (schemeSlice B S hS U) (schemeSliceEquivalenceOver B S hS U)) ?_
    rw [hfac]
    exact hopenChart


/-- **Stacks 0512, the forward implication.** A universally closed representable 1-morphism has
first projection closed on points after every base change by an algebraic stack.

Take a chart of `𝒵` by the slice of the site over a scheme `U`, open and surjective on points by
`AlgebraicGeometry.Stack.exists_sliceChart_isOpenMap_surjective`. Universal closedness, read on
the lower-shriek extension at the scheme-valued point of `𝒴` the chart names, says the structural
morphism of the presheaf representing the base change is a closed morphism of algebraic spaces;
that is closedness on points of the first projection of the canonical square over the point, by
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_iff_isClosedMorphism_representingMap` and
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`; the first-factor cancellation of
Tag 02XD and
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr` move it to `U ×_𝒵 (𝒵 ×_𝒴 𝒳)`; and the
open surjection descends it, the hypothesis on the canonical map to the topological fibre product
being Tag 04XH. -/
theorem isClosedMap_pointsMap_fst_of_universallyClosed
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (H : UniversallyClosed B S hS f.hom)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴) :
    @IsClosedMap _ _
      (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
      (pointTopology B S hS 𝒵.val)
      (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom) := by
  classical
  obtain ⟨U, c, hcsurj, hcopen⟩ := exists_sliceChart_isOpenMap_surjective B S hS 𝒵
  let cMor : schemeSlice B S hS U ⟶ 𝒵.val := Bicategory.InducedBicategory.mkHom c
  let y := CatFiberedInGroupoids.homFunctor (cMor ≫ g.hom)
  have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom :=
    CatFiberedInGroupoids.homFunctor_comp_p (cMor ≫ g.hom)
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let Pb := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom
  let V := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Pb.fst cMor
  obtain ⟨T, hT, heT⟩ := hf U y hy
  obtain ⟨eT⟩ := heT
  have hUC := (universallyClosed_iff_forall_relocalize B S hS f.hom).mp H U y hy T hT ⟨eT⟩
  have hCM : Space.IsClosedMorphism B S hS (OverShriek.relocalizeToYoneda U.hom T) :=
    MorphismProperty.universally_le (Space.isClosedMorphismProperty B S hS) _
      ((Space.universallyClosed_iff_universally_isClosedMorphism B S hS
        (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
          (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
              isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
            AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
            AlgebraicSpaces B S hS))).mp hUC)
  have hQc : @IsClosedMap _ _
      (pointTopology B S hS
        Q.pt)
      (pointTopology B S hS (schemeSlice B S hS U))
      (pointsMap B S hS
        Q.pt.val
        Q.pt.property
        (schemeSlice B S hS U).property
        Q.fst.hom) := by
    refine (isClosedMap_pointsMap_iff_isClosedMorphism_representingMap B S hS
      Q.pt
      (schemeSlice B S hS U)
      ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
      (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
      (isAlgebraicSpace_yoneda B S hS U)
      (relocalizeFibreEquivalence B S hS U f.hom y T eT)
      (schemeSliceEquivalenceOver B S hS U)
      Q.fst).mpr ?_
    rw [representingMap_relocalizeFibre B S hS U f.hom y T eT hy]
    exact hCM
  have hRclosed := isClosedMap_pointsMap_fst_congr B S hS
    Q
    (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} g.hom f.hom cMor
      (schemeSliceMap B S hS U y hy) (Iso.refl _)).swap
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f.hom)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
        g.hom f.hom cMor (schemeSliceMap B S hS U y hy) (Iso.refl _))) hQc
  refine @isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective
    (points B S hS
      V.pt.val _)
    (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property)
    (points B S hS
      Pb.pt.val _)
    (points B S hS 𝒵.val.val 𝒵.val.property)
    (pointTopology B S hS
      V.pt)
    (pointTopology B S hS (schemeSlice B S hS U))
    (pointTopology B S hS
      Pb.pt)
    (pointTopology B S hS 𝒵.val)
    (pointsMap B S hS
      V.pt.val _ (schemeSlice B S hS U).property
      V.snd.hom)
    (pointsMap B S hS
      V.pt.val _ _
      V.fst.hom)
    (pointsMap B S hS
      Pb.pt.val _
      𝒵.val.property
      Pb.fst.hom)
    (pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
      𝒵.val.property c)
    (fun x => ?_) hcopen hcsurj
    (continuous_pointsMap B S hS
      V.pt
      Pb.pt
      V.fst.hom)
    (fun v cc h => ?_) hRclosed
  · exact ((pointsMap_comp B S hS _ _ (schemeSlice B S hS U).property 𝒵.val.property
        V.snd.hom cMor.hom x).trans
      (congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ 𝒵.val.property
        V.iso.inv.hom) x)).trans
      (pointsMap_comp B S hS _ _ _ 𝒵.val.property
        V.fst.hom
        Pb.fst.hom
        x).symm
  · obtain ⟨r, hr1, hr2⟩ := exists_point_of_isTwoFibreProduct B S hS
      V
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Pb.fst cMor)
      cc v h.symm
    exact ⟨r, hr2, hr1⟩


/-- **Stacks 0512, the converse implication.** A representable 1-morphism whose first projection
is closed on points after every base change by an algebraic stack is universally closed.

It is enough to see that the structural morphism `Λ_U T ⟶ h_U` of the lower-shriek extension of a
presheaf representing a base change along a scheme-valued point is universally closed, that is,
that `|Z ×_{h_U} Λ_U T| → |Z|` is closed for every algebraic space `Z` over `h_U`. The morphism
`k : Z ⟶ h_U` comes from a 1-morphism out of the category of elements of `Z` (Tag 04SW, onto);
the hypothesis at that algebraic stack, moved by two first-factor cancellations of Tag 02XD and
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_fst_congr`, is closedness on points of the first
projection of `Z ×_U (U ×_𝒴 𝒳)`;
`AlgebraicGeometry.Stack.isClosedMap_pointsMap_iff_isClosedMorphism_representingMap` reads that on
the representing presheaves; and Tag 04SD identifies that representing presheaf with the fibre
product `Z ×_{h_U} Λ_U T`. -/
theorem universallyClosed_of_isClosedMap_pointsMap_fst
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (Hpts : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
      @IsClosedMap _ _
        (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
        (pointTopology B S hS 𝒵.val)
        (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
          (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom)) :
    UniversallyClosed B S hS f.hom := by
  classical
  rw [universallyClosed_iff_forall_relocalize]
  intro U y hy T hT heT
  obtain ⟨eT⟩ := heT
  intro Z hZ k
  -- the two represented algebraic stacks and the 1-morphism inducing `k`
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeSlice B S hS U, isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS
      (schemeSlice B S hS U) (isRepresentableByAlgebraicSpace_schemeSlice B S hS U)⟩
  let Zalg : AlgebraicStacks.{u, w} B S hS :=
    ⟨fibredCategory B S hS Z, isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ⟩
  obtain ⟨hZU, hk⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := Zalg) (𝒴 := Ualg) Z (yoneda.obj U)
    (spaceEquivalenceOver B S hS Z) (schemeSliceEquivalenceOver B S hS U) k
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let gZ := hZU ≫ Bicategory.InducedBicategory.mkHom (schemeSliceMap B S hS U y hy)
  let R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom Q.fst
  -- the canonical square over the scheme-valued point, and its representing data
  have hQrep := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳.val 𝒴.val
    (schemeSlice B S hS U) f.hom (schemeSliceMap B S hS U y hy)
    Q
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f.hom) hf
  have hQfst_rep := representingMap_relocalizeFibre B S hS U f.hom y T eT hy
  -- the hypothesis at the represented stack `Z`
  have hHyp := Hpts Zalg
    gZ
  -- cancel the middle factor, twice, to read it on `Z ×_U (U ×_𝒴 𝒳)`
  have h1 := isClosedMap_pointsMap_fst_congr B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      gZ.hom f.hom)
    (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f.hom hZU.hom
      gZ.hom
      (Iso.refl _)).swap
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      gZ.hom f.hom)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f.hom hZU.hom
        gZ.hom
        (Iso.refl _))) hHyp
  have h2 := isClosedMap_pointsMap_fst_congr B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      Q.fst hZU.hom).swap
    R
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.fst hZU.hom))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom
      Q.fst) h1
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    Q.pt (schemeSlice B S hS U) (fibredCategory B S hS Z) Q.fst hZU.hom
    R
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      hZU.hom Q.fst) hQrep (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  have h3 := (isClosedMap_pointsMap_iff_isClosedMorphism_representingMap B S hS
    R.pt
    (fibredCategory B S hS Z) W Z hW hZ eW (spaceEquivalenceOver B S hS Z)
    R.fst).mp h2
  rw [← hk, ← hQfst_rep]
  let _inst : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS Z) Q.pt
      (schemeSlice B S hS U) hZU.hom Q.fst).IsFibered :=
    R.pt.property.isFibered
  have hA := fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS
    (fibredCategory B S hS Z) Q.pt (schemeSlice B S hS U) Z
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
    (spaceEquivalenceOver B S hS Z) (relocalizeFibreEquivalence B S hS U f.hom y T eT)
    (schemeSliceEquivalenceOver B S hS U) hZU.hom Q.fst W eW
  have hiso : Arrow.mk (ObjectProperty.homMk (pullback.fst
        (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
        (representingMap B S hS Q.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Q.fst)) :
      (⟨pullback (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
          (representingMap B S hS Q.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Q.fst),
        isAlgebraicSpace_pullback B S hS _ _ hZ
          (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
          (isAlgebraicSpace_yoneda B S hS U)⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (representingMap B S hS R.pt (fibredCategory B S hS Z) W Z eW
          (spaceEquivalenceOver B S hS Z) R.fst) :
        (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) := by
    refine Arrow.isoMk (ObjectProperty.isoMk _
      ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (fibredCategory B S hS Z) Q.pt
          (schemeSlice B S hS U) Z ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom Q.fst W eW)) (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (fibredCategory B S hS Z) Q.pt
          (schemeSlice B S hS U) Z ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom Q.fst W eW).hom ≫
        (representingMap B S hS R.pt (fibredCategory B S hS Z) W Z eW
          (spaceEquivalenceOver B S hS Z) R.fst) =
      pullback.fst (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
        (representingMap B S hS Q.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Q.fst) ≫ 𝟙 _
    rw [Category.comp_id, Iso.trans_hom, Category.assoc, hA, Iso.symm_hom]
    exact (Presheaf.isPullback_fibreProduct _ _).isoPullback_inv_fst
  exact ((Space.isClosedMorphismProperty B S hS).arrow_mk_iso_iff hiso).mpr h3


/-- **Stacks 0512.** A 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces is universally closed — the relative property of Tag 04XB at universal
closedness of morphisms of algebraic spaces — exactly when, for every algebraic stack `𝒵` over
`𝒴`, the first projection of the canonical 2-fibre product of Tag 04T2 is a closed map on the
points of Tag 04XL. -/
@[stacks 0512]
theorem representable_universallyClosed_iff_closedMap_baseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    UniversallyClosed B S hS f.hom ↔
      ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
        let P := twoFibreProductSquareAlgebraicStacks B S hS g f
        @IsClosedMap
          (points B S hS P.pt.val.val (Classical.choose P.pt.property))
          (points B S hS 𝒵.val.val (Classical.choose 𝒵.property))
          (pointTopology B S hS P.pt.val)
          (pointTopology B S hS 𝒵.val)
          (pointsMap B S hS P.pt.val.val
            (Classical.choose P.pt.property) (Classical.choose 𝒵.property)
            P.fst.hom.hom) := by
  constructor
  · intro H 𝒵 g
    exact isClosedMap_pointsMap_fst_of_universallyClosed B S hS f hf H 𝒵 g
  · intro Hpts
    exact universallyClosed_of_isClosedMap_pointsMap_fst B S hS f hf Hpts

end AlgebraicGeometry.Stack



end

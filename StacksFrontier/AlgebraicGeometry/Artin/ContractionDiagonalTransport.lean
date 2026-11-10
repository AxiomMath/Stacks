module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalHypotheses
import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseClosedImmersion
import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSubspaces
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionGluing
import StacksFrontier.AlgebraicGeometry.FormalSpace.EquivalenceRelationFromCompletion
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# The hypotheses of Stacks 0GHE for the triple of Stacks 0GHD (4)

In the situation of Stacks 0GH8 let `V` be a locally Noetherian scheme over `S` and `d` the data of
Stacks 0GHD over `V`. Assertion (4) of Stacks 0GHD makes `E'`, `(E' ⟶ V)⁻¹ Z` and
`E'_{/Z} ⟶ E_W` a situation over the base `V`
(`AlgebraicGeometry.Artin.ContractionEqualizer.situation`), through the change of base of Stacks
04SG. Stacks 0GHE is applied to that situation with the closed subset `Z ⊆ V`; this file reads its
hypotheses over `V` from their counterparts over `S`:

* `AlgebraicGeometry.Artin.ContractionEqualizer.isProper_terminal_from`: `E'` is proper over `V`
  when `E' ⟶ V` is proper over `S`;
* `AlgebraicGeometry.Artin.ContractionEqualizer.ZOverV`,
  `AlgebraicGeometry.Artin.ContractionEqualizer.isClosed_ZOverV` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.preimage_ZOverV`: the closed subset `Z` of the base
  `V`, whose inverse image in `E'` is `(E' ⟶ V)⁻¹ Z`;
* `AlgebraicGeometry.Artin.ContractionEqualizer.openPartMap` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.isClosedImmersion_openPartMap`: the morphism
  `U' ⟶ V ∖ Z` and its being a closed immersion, from `E' ×_V (V ∖ Z) ⟶ V ∖ Z`;
* `AlgebraicGeometry.Artin.ContractionEqualizer.formalPartMap` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.isClosedImmersion_formalPartMap`: the morphism
  `E_W ⟶ V_{/Z}` over `V` and its being a closed immersion, from `E_W ⟶ V_{/Z}` over `S` through
  `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_smallerBaseSheafFunctor_map`.

The base of a situation over `V` is the terminal presheaf on the big fppf site of `V`; the
equivalence of Stacks 04SG sends the terminal object of the presheaves over `V` to a terminal
presheaf (`AlgebraicGeometry.Artin.ContractionEqualizer.baseVIso`), which is how the sets of points
and the morphisms over `S` are carried to the terminal presheaf over `V`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
* [Stacks Project, Tag 0GHF](https://stacks.math.columbia.edu/tag/0GHF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- **Closed immersions over a smaller base.** A morphism of presheaves over the representable
presheaf of `g : V ⟶ S` whose underlying morphism is a closed immersion over `S` induces a
closed immersion of the attached presheaves over `V` (Stacks 04SG together with
`AlgebraicGeometry.Space.isClosedImmersion_relocalizeMap_iff`). -/
theorem isClosedImmersion_smallerBaseInverse_map
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.left) :
    IsClosedImmersion B V hV ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) := by
  have := isClosedImmersion_respectsIso B S hS
  rw [← isClosedImmersion_relocalizeMap_iff B V S hV hS g]
  have h := smallerBaseInverseRelocalizeIso_hom_naturality B V S hV hS g f
  rw [← Iso.eq_comp_inv, Category.assoc] at h
  rw [h]
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion B S hS) _ _).2
    ((MorphismProperty.cancel_right_of_respectsIso (@IsClosedImmersion B S hS) _ _).2 hf)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- The terminal object of the presheaves over `V`. -/
abbrev overVTerminal : Over (yoneda.obj (Over.mk (V.hom : B.obj V.left.property ⟶ B.obj hS)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk (𝟙 _)

variable (V) in
/-- The presheaf over `V` attached to the terminal object of the presheaves over `V`. -/
abbrev baseV : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u :=
  (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.obj
    (overVTerminal (V := V))

variable (V) in
/-- The presheaf `baseV V` is terminal. -/
def baseVIso : baseV V ≅ ⊤_ ((BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u) :=
  (Over.mkIdTerminal.isTerminalObj
    (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse
      _).uniqueUpToIso
    terminalIsTerminal

/-- The morphism `E' ⟶ V`, as a morphism of presheaves over `V`. -/
abbrev toOverVTerminal : d.E'OverV ⟶ overVTerminal := Over.homMk d.toBase

/-- The structure morphism of the algebraic space `E'` of the situation of Stacks 0GHD (4) is
attached to `E' ⟶ V`. -/
theorem terminal_from_eq (hVN : IsLocallyNoetherian V.left.obj) :
    terminal.from (d.situation hVN).X' =
      (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
        d.toOverVTerminal ≫ (baseVIso V).hom :=
  terminal.hom_ext _ _

/-- If `E' ⟶ V` is proper, the algebraic space of the situation of Stacks 0GHD (4) is proper
over `V`. -/
theorem isProper_terminal_from (hp : Space.IsProper B S hS d.toBase)
    (hVN : IsLocallyNoetherian V.left.obj) :
    Space.IsProper B V.left.obj V.left.property (terminal.from (d.situation hVN).X') := by
  rw [d.terminal_from_eq hVN]
  refine (Space.isProper_comp_isIso_iff B V.left.obj V.left.property _ _).2 ?_
  exact Space.isProper_smallerBaseInverse_map B V.left.obj S V.left.property hS V.hom _
    d.isAlgebraicSpace_eqz (isAlgebraicSpace_yoneda B S hS _) hp

/-- The closed subset `Z ⊆ |V|`, read on the terminal presheaf over `V`. -/
def ZOverV : Set (Space.points B V.left.obj V.left.property
    (⊤_ ((BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u))) :=
  (fun p => Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
    overVTerminal (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv p)) ⁻¹' d.Z

/-- The set `ZOverV` is closed. -/
theorem isClosed_ZOverV : IsClosed d.ZOverV :=
  d.isClosed_Z.preimage ((Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property
    hS V.hom overVTerminal).continuous.comp (Space.continuous_pointsMap _ _ _ _))

/-- The inverse image of `ZOverV` under any morphism from `E'`, viewed over `V`, to the terminal
presheaf is `(E' ⟶ V)⁻¹ Z`, viewed over `V`. -/
theorem preimage_ZOverV_of_eq
    (t : (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.obj
      d.E'OverV ⟶ ⊤_ ((BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u)) :
    Space.pointsMap B V.left.obj V.left.property _ t ⁻¹' d.ZOverV =
      Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom d.E'OverV
        d.centerEqz := by
  have ht : t = (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
      d.toOverVTerminal ≫ (baseVIso V).hom := terminal.hom_ext _ _
  ext y
  have key : Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv
      (Space.pointsMap B V.left.obj V.left.property _ t y) =
      Space.pointsMap B V.left.obj V.left.property _
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
          d.toOverVTerminal) y := by
    rw [← Function.comp_apply (f := Space.pointsMap _ _ _ _ (baseVIso V).inv),
      ← Space.pointsMap_comp, ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
    overVTerminal (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv
      (Space.pointsMap B V.left.obj V.left.property _ t y)) ∈ d.Z ↔ _
  rw [key, Space.pointsSmallerBaseInverseHomeomorph_naturality]
  rfl

/-- The inverse image of `ZOverV` in the algebraic space of the situation of Stacks 0GHD (4) is
its closed subset. -/
theorem preimage_ZOverV (hVN : IsLocallyNoetherian V.left.obj) :
    Space.pointsMap B V.left.obj V.left.property _ (terminal.from (d.situation hVN).X') ⁻¹'
      d.ZOverV = (d.situation hVN).T' :=
  d.preimage_ZOverV_of_eq _

/-- `E' ∖ (E' ⟶ V)⁻¹ Z`, as a presheaf over `V`. -/
abbrev openPartOverV : Over (yoneda.obj (Over.mk (V.hom : B.obj V.left.property ⟶ B.obj hS)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase)

/-- `V ∖ Z`, as a presheaf over `V`. -/
abbrev offCenterOverV : Over (yoneda.obj (Over.mk (V.hom : B.obj V.left.property ⟶ B.obj hS)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk (d.offCenter.ι ≫ (overVTerminal (V := V)).hom)

/-- `E' ∖ (E' ⟶ V)⁻¹ Z` lies over `V ∖ Z`. -/
theorem centerEqz_compl_subset :
    d.centerEqzᶜ ⊆ Space.pointsMap B S hS d.eqz d.toBase ⁻¹' d.Zᶜ := fun _ h => h

/-- The morphism `E' ∖ (E' ⟶ V)⁻¹ Z ⟶ V ∖ Z` of algebraic spaces over `S`. -/
abbrev openPartRestrict :
    (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).toFunctor ⟶ d.offCenter.toFunctor :=
  Space.openSubspaceOfPointsRestrict B S hS d.toBase d.centerEqzᶜ d.Zᶜ d.centerEqz_compl_subset

/-- The morphism `E' ∖ (E' ⟶ V)⁻¹ Z ⟶ V ∖ Z` over `V`. -/
def openPartToOffCenter : d.openPartOverV ⟶ d.offCenterOverV :=
  Over.homMk d.openPartRestrict (by
    change d.openPartRestrict ≫ d.offCenter.ι ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _)

/-- If `E' ⟶ V` is proper, `E' ∖ (E' ⟶ V)⁻¹ Z ⟶ V ∖ Z` is a closed immersion: it is the base
change `E' ×_V (V ∖ Z) ⟶ V ∖ Z`. -/
theorem isClosedImmersion_openPartToOffCenter_left (hp : Space.IsProper B S hS d.toBase) :
    Space.IsClosedImmersion B S hS d.openPartToOffCenter.left := by
  have := Space.isClosedImmersion_respectsIso B S hS
  have hsq := FormalSpace.isPullback_ι_openSubspaceOfPoints_compl B S hS d.toBase d.Z
    d.openPartRestrict (Space.openSubspaceOfPointsRestrict_comp_ι B S hS _ _ _ _)
  change Space.IsClosedImmersion B S hS d.openPartRestrict
  rw [← hsq.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso (@Space.IsClosedImmersion B S hS) _ _).2
    (d.isClosedImmersion_pullbackSnd_offCenter hp)

/-- The complement of `Z`, read on `baseV V`, lies over the complement of `ZOverV`. -/
theorem subset_preimage_ZOverV_compl :
    Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
        overVTerminal ⁻¹' d.Zᶜ ⊆
      Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom ⁻¹' d.ZOverVᶜ := by
  intro y hy
  change Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
    overVTerminal (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv
      (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom y)) ∉ d.Z
  rw [← Function.comp_apply (f := Space.pointsMap _ _ _ _ (baseVIso V).inv),
    ← Space.pointsMap_comp, Iso.hom_inv_id, Space.pointsMap_id]
  exact hy

/-- The comparison of the open subspace `V ∖ Z` read on `baseV V` and on the terminal presheaf. -/
def offCenterComparison :
    (Space.openSubspaceOfPoints B V.left.obj V.left.property (baseV V)
      (Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
        overVTerminal ⁻¹' d.Zᶜ)).toFunctor ⟶
      (Space.openSubspaceOfPoints B V.left.obj V.left.property _ d.ZOverVᶜ).toFunctor :=
  Space.openSubspaceOfPointsRestrict B V.left.obj V.left.property (baseVIso V).hom _ _
    d.subset_preimage_ZOverV_compl

/-- The comparison `offCenterComparison` is a closed immersion, being a base change of an
isomorphism. -/
theorem isClosedImmersion_offCenterComparison :
    Space.IsClosedImmersion B V.left.obj V.left.property d.offCenterComparison := by
  have hW : Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
        overVTerminal ⁻¹' d.Zᶜ =
      (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom ⁻¹' d.ZOverV)ᶜ := by
    ext y
    change Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
      overVTerminal y ∉ d.Z ↔ Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S
        V.left.property hS V.hom overVTerminal (Space.pointsMap B V.left.obj V.left.property _
          (baseVIso V).inv (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom y))
          ∉ d.Z
    rw [← Function.comp_apply (f := Space.pointsMap _ _ _ _ (baseVIso V).inv),
      ← Space.pointsMap_comp, Iso.hom_inv_id, Space.pointsMap_id]
    rfl
  have hsq := FormalSpace.isPullback_ι_openSubspaceOfPoints_of_eq
    (baseVIso V).hom d.ZOverV hW d.offCenterComparison
    (Space.openSubspaceOfPointsRestrict_comp_ι B V.left.obj V.left.property _ _ _ _)
  exact (Space.isClosedImmersion_isStableUnderBaseChange B V.left.obj V.left.property).of_isPullback
    hsq (Space.isClosedImmersion_of_isIso B V.left.obj V.left.property _)

/-- The morphism `U' ⟶ V ∖ Z` of the situation of Stacks 0GHD (4) over `V`. -/
def openPartMap (hVN : IsLocallyNoetherian V.left.obj) :
    (d.situation hVN).U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B V.left.obj V.left.property _ d.ZOverVᶜ).toFunctor :=
  (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom d.E'OverV
      d.centerEqzᶜ).hom ≫
    (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
      d.openPartToOffCenter ≫
    (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom overVTerminal
      d.Zᶜ).inv ≫ d.offCenterComparison

/-- If `E' ⟶ V` is proper, the morphism `U' ⟶ V ∖ Z` of the situation of Stacks 0GHD (4) over
`V` is a closed immersion. -/
theorem isClosedImmersion_openPartMap (hp : Space.IsProper B S hS d.toBase)
    (hVN : IsLocallyNoetherian V.left.obj) :
    Space.IsClosedImmersion B V.left.obj V.left.property (d.openPartMap hVN) := by
  have := Space.isClosedImmersion_isStableUnderComposition B V.left.obj V.left.property
  have h₁ := Space.isClosedImmersion_of_isIso B V.left.obj V.left.property
    (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom d.E'OverV
      d.centerEqzᶜ).hom
  have h₃ := Space.isClosedImmersion_of_isIso B V.left.obj V.left.property
    (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom overVTerminal
      d.Zᶜ).inv
  have h₂ := Space.isClosedImmersion_smallerBaseInverse_map B V.left.obj S V.left.property hS
    V.hom _ (d.isClosedImmersion_openPartToOffCenter_left hp)
  exact MorphismProperty.comp_mem _ _ _ h₁ (MorphismProperty.comp_mem _ _ _ h₂
    (MorphismProperty.comp_mem _ _ _ h₃ d.isClosedImmersion_offCenterComparison))

/-! ### The closed immersion `E_W ⟶ V_{/Z}` over `V` -/

/-- The completion of `V` along `Z`, read over `V` on `baseV V`. -/
abbrev completionOverV : FormalSpace.FppfSheaf B V.left.obj V.left.property :=
  Space.completionSheaf B V.left.obj V.left.property (baseV V)
    (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom overVTerminal d.Z)

/-- The morphism `E_W ⟶ V_{/Z}` read on the attached sheaves. -/
def completedEWMapAttached :
    (FormalSpace.smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).obj
        (FormalSpace.smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW
          d.EWToTarget) ⟶
      (FormalSpace.smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).obj
        d.completionOverV :=
  (FormalSpace.smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW
      d.EWToTarget).hom ≫ equalizer.ι d.xhat₁ d.xhat₂ ≫
    (ContractionSituation.smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
      overVTerminal (isAlgebraicSpace_yoneda B S hS _) d.Z).inv

/-- The morphism `completedEWMapAttached` is compatible with the structure morphisms to `V`. -/
theorem completedEWMapAttached_comp_str :
    d.completedEWMapAttached ≫
        FormalSpace.smallerBaseStr B V.left.obj S V.left.property hS V.hom d.completionOverV =
      FormalSpace.smallerBaseStr B V.left.obj S V.left.property hS V.hom
        (FormalSpace.smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW
          d.EWToTarget) := by
  rw [← FormalSpace.smallerBaseSheafOfIso_hom_comp, completedEWMapAttached, Category.assoc]
  congr 1
  apply Sheaf.hom_ext
  have h := ContractionSituation.smallerBaseCompletionIso_hom_comp B V.left.obj S V.left.property
    hS V.hom overVTerminal (isAlgebraicSpace_yoneda B S hS _) d.Z
  rw [EWToTarget_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  congr 1
  have e : (ContractionSituation.smallerBaseCompletionIso B V.left.obj S V.left.property hS
        V.hom overVTerminal (isAlgebraicSpace_yoneda B S hS _) d.Z).inv.hom ≫
      (ContractionSituation.smallerBaseCompletionIso B V.left.obj S V.left.property hS
        V.hom overVTerminal (isAlgebraicSpace_yoneda B S hS _) d.Z).hom.hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
    rfl
  rw [← h]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
    ((Category.id_comp _).trans ?_))
  rw [Space.completionSheafToSmallerBase,
    Space.completionSheafToAmbient_eq B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf]
  rfl

/-- The morphism `E_W ⟶ V_{/Z}` over `V`. -/
def completedEWMap :
    FormalSpace.smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget ⟶
      d.completionOverV :=
  FormalSpace.smallerBaseLift B V.left.obj S V.left.property hS V.hom d.completedEWMapAttached
    d.completedEWMapAttached_comp_str

/-- If `E_W ⟶ V_{/Z}` is a closed immersion over `S`, it is one over `V`. -/
theorem isClosedImmersion_completedEWMap
    (hEW : FormalSpace.IsClosedImmersion B S hS (equalizer.ι d.xhat₁ d.xhat₂)) :
    FormalSpace.IsClosedImmersion B V.left.obj V.left.property d.completedEWMap := by
  refine FormalSpace.isClosedImmersion_of_smallerBaseSheafFunctor_map B V.left.obj S
    V.left.property hS V.hom _ ?_
  rw [completedEWMap, FormalSpace.smallerBaseSheafFunctor_map_smallerBaseLift,
    completedEWMapAttached]
  exact FormalSpace.isClosedImmersion_comp B S hS _ _
    (FormalSpace.isClosedImmersion_of_isIso B S hS _)
    (FormalSpace.isClosedImmersion_comp B S hS _ _ hEW
      (FormalSpace.isClosedImmersion_of_isIso B S hS _))

/-- `Z`, read on `baseV V`, lies over `ZOverV`. -/
theorem subset_preimage_ZOverV :
    Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom overVTerminal d.Z ⊆
      Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom ⁻¹' d.ZOverV := by
  intro y hy
  change Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
    overVTerminal (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv
      (Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).hom y)) ∈ d.Z
  rw [← Function.comp_apply (f := Space.pointsMap _ _ _ _ (baseVIso V).inv),
    ← Space.pointsMap_comp, Iso.hom_inv_id, Space.pointsMap_id]
  exact hy

/-- `ZOverV` lies over `Z`, read on `baseV V`. -/
theorem ZOverV_subset_preimage : d.ZOverV ⊆
    Space.pointsMap B V.left.obj V.left.property _ (baseVIso V).inv ⁻¹'
      Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom overVTerminal d.Z :=
  fun _ h => h

/-- The completion of `V` along `Z` read on `baseV V` and on the terminal presheaf. -/
def completionOverVIso : d.completionOverV ≅
    Space.completionSheaf B V.left.obj V.left.property _ d.ZOverV where
  hom := Space.completionSheafRestrict B V.left.obj V.left.property (baseVIso V).hom _ _
    d.subset_preimage_ZOverV
  inv := Space.completionSheafRestrict B V.left.obj V.left.property (baseVIso V).inv _ _
    d.ZOverV_subset_preimage
  hom_inv_id := (Space.completionSheafRestrict_comp_eq B V.left.obj V.left.property _ _ (𝟙 _)
      (Iso.hom_inv_id _) _ _ _ _ _
      (Space.subset_preimage_pointsMap_id B V.left.obj V.left.property subset_rfl)).trans
    (Space.completionSheafRestrict_id B V.left.obj V.left.property _ _)
  inv_hom_id := (Space.completionSheafRestrict_comp_eq B V.left.obj V.left.property _ _ (𝟙 _)
      (Iso.inv_hom_id _) _ _ _ _ _
      (Space.subset_preimage_pointsMap_id B V.left.obj V.left.property subset_rfl)).trans
    (Space.completionSheafRestrict_id B V.left.obj V.left.property _ _)

/-- The morphism `W ⟶ V_{/Z}` of the situation of Stacks 0GHD (4) over `V`. -/
def formalPartMap (hVN : IsLocallyNoetherian V.left.obj) :
    (d.situation hVN).W ⟶ Space.completionSheaf B V.left.obj V.left.property _ d.ZOverV :=
  d.completedEWMap ≫ d.completionOverVIso.hom

/-- If `E_W ⟶ V_{/Z}` is a closed immersion over `S`, the morphism `W ⟶ V_{/Z}` of the situation
of Stacks 0GHD (4) over `V` is a closed immersion. -/
theorem isClosedImmersion_formalPartMap
    (hEW : FormalSpace.IsClosedImmersion B S hS (equalizer.ι d.xhat₁ d.xhat₂))
    (hVN : IsLocallyNoetherian V.left.obj) :
    FormalSpace.IsClosedImmersion B V.left.obj V.left.property (d.formalPartMap hVN) :=
  FormalSpace.isClosedImmersion_comp B V.left.obj V.left.property _ _
    (d.isClosedImmersion_completedEWMap hEW)
    (FormalSpace.isClosedImmersion_of_isIso B V.left.obj V.left.property _)

end AlgebraicGeometry.Artin.ContractionEqualizer

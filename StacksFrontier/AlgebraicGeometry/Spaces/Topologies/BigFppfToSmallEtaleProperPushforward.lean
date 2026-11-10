module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct image along a proper morphism and the big fppf topos of an algebraic space (Stacks 0DGJ)

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : Y ⟶ X` a morphism of algebraic
spaces of `T`. The commutative square of topoi of Stacks 0DGI,
`f_{small,*} ∘ a_{Y,*} = a_{X,*} ∘ f_{big,fppf,*}`, has a canonical mate

`a_X⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_Y⁻¹`,

here `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleBaseChange`. Stacks 0DGJ, part (1),
asserts that it is an isomorphism when `f` is proper.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleBaseChange`: the canonical base change
  map, the mate of the square of Stacks 0DGI across `a_Y⁻¹ ⊣ a_{Y,*}` and `a_X⁻¹ ⊣ a_{X,*}`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtalePushforwardIsoOfIsProper`: the
  isomorphism `a_X⁻¹ ∘ f_{small,*} ≅ f_{big,fppf,*} ∘ a_Y⁻¹` for `f` proper.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleBaseChange_of_isProper`: the
  canonical base change map is an isomorphism when `f` is proper.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleBaseChange_eq_vComp`: the canonical map
  is the base change map of Stacks 0DGD for `π` followed by the mate of the big square of
  Stacks 0DGI for `ε`.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtaleMorphism_counit`: the counit of
  `ε_X⁻¹ ⊣ ε_{X,*}` is an isomorphism.

## References

* [Stacks Project, Tag 0DGJ](https://stacks.math.columbia.edu/tag/0DGJ)
* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
-/

@[expose] public noncomputable section

open CategoryTheory TwoSquare

universe u

namespace CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The mate of a square of right adjoints followed by a change `θ : H ⟶ H'` of its bottom-left
functor is the mate of the square followed by `θ` on the other side. -/
theorem mateEquiv_symm_whiskerLeft (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare R₁ H G R₂)
    (θ : H ⟶ H') :
    (mateEquiv adj₁ adj₂).symm (α.whiskerLeft θ) =
      ((mateEquiv adj₁ adj₂).symm α).whiskerBottom θ := by
  ext c
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerBottom]

/-- The mate of an invertible square of right adjoints is invertible at an object `c` once the
unit of the first adjunction is invertible at `c` and the counit of the second one is invertible
at the image of `c`. -/
theorem isIso_mateEquiv_symm_app_of_isIso_unit_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : R₁ ⋙ G ≅ H ⋙ R₂) (c : C) [IsIso (adj₁.unit.app c)]
    [IsIso (adj₂.counit.app (H.obj (L₁.obj c)))] :
    IsIso (((mateEquiv adj₁ adj₂).symm α.hom).app c) := by
  simp only [Functor.comp_obj, mateEquiv, Equiv.symm_mk, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.map_id,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    isIso_comp_left_iff]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- The comparison `smallBaseChange_comp_inclusionIso T f` of site functors is the identity on each
étale chart: both cartesian squares are the chosen fibre product. -/
theorem smallBaseChange_comp_inclusionIso_hom_app_eq_id {X Y : T.Spaces} (f : Y ⟶ X)
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X) :
    (smallBaseChange_comp_inclusionIso T f).hom.app U = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply (IsPullback.of_hasPullback U.1.hom f).hom_ext <;>
  · simp only [smallBaseChange_comp_inclusionIso, smallBaseChange_comp_inclusionIsoApp]
    simp
    rfl

/-- The comparison `smallBaseChange_comp_inclusionIso T f` of site functors is the identity
isomorphism. -/
theorem smallBaseChange_comp_inclusionIso_eq_refl {X Y : T.Spaces} (f : Y ⟶ X) :
    smallBaseChange_comp_inclusionIso T f = Iso.refl _ :=
  Iso.ext (NatTrans.ext (funext (smallBaseChange_comp_inclusionIso_hom_app_eq_id T f)))

/-- The inverse of the comparison `smallBaseChange_comp_inclusionIso T f` of site functors is the
identity on each étale chart. -/
theorem smallBaseChange_comp_inclusionIso_inv_app_eq_id {X Y : T.Spaces} (f : Y ⟶ X)
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X) :
    (smallBaseChange_comp_inclusionIso T f).inv.app U = 𝟙 _ := by
  rw [smallBaseChange_comp_inclusionIso_eq_refl]
  rfl

/-- Restriction along the comparison `smallBaseChange_comp_inclusionIso T f` of site functors is
the identity isomorphism of restriction functors. -/
theorem sheafPushforwardContinuousIso_smallBaseChange_comp_inclusionIso {X Y : T.Spaces}
    (f : Y ⟶ X) :
    letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
    letI := (inclusion_isMorphismOfSites T Y).isContinuous
    letI := (inclusion_isMorphismOfSites T X).isContinuous
    letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
    letI := Functor.isContinuous_comp
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      (T.bigEtaleTopology Y)
    letI := Functor.isContinuous_comp
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comp_inclusionIso T f)
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology Y) = Iso.refl _ := by
  ext M : 3
  ext U x
  simp only [Functor.sheafPushforwardContinuousIso_hom_app_hom_app,
    smallBaseChange_comp_inclusionIso_inv_app_eq_id]
  exact M.obj.map_id_apply _ x

/-- The square `T.bigSmallEtale_pushforwardCommIso f` is the square
`bigSmallEtalePullbackSquare T f` followed by the identification of the big étale direct image with
restriction along `Over.pullback f`. -/
theorem bigSmallEtale_pushforwardCommIso_hom_eq {X Y : T.Spaces} (f : Y ⟶ X) :
    (T.bigSmallEtale_pushforwardCommIso f).hom =
      (bigSmallEtalePullbackSquare T f).hom ≫
        Functor.whiskerRight (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).inv
          (bigToSmallEtaleMorphism T X).pushforward := by
  let := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  let := (inclusion_isMorphismOfSites T Y).isContinuous
  let := (inclusion_isMorphismOfSites T X).isContinuous
  let := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  let := Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology Y)
  let := Functor.isContinuous_comp
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  change (Functor.sheafPushforwardContinuousComp
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Type (u + 1))
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      (T.bigEtaleTopology Y) ≪≫
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comp_inclusionIso T f)
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X) (T.bigEtaleTopology Y)).symm ≪≫
    Functor.isoWhiskerRight
      (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).symm
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X))).hom = _
  rw [sheafPushforwardContinuousIso_smallBaseChange_comp_inclusionIso]
  rfl

/-- The mate of the square `T.bigSmallEtale_pushforwardCommIso f` is the base change map
`bigToSmallEtaleBaseChange T f : π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`, followed by the
identification of the big étale direct image with restriction along `Over.pullback f`. -/
theorem mateEquiv_symm_bigSmallEtale_pushforwardCommIso {X Y : T.Spaces} (f : Y ⟶ X) :
    ((mateEquiv (bigToSmallEtaleMorphism T Y).adj (bigToSmallEtaleMorphism T X).adj).symm
        (T.bigSmallEtale_pushforwardCommIso f).hom) =
      bigToSmallEtaleBaseChange T f ≫ Functor.whiskerLeft _
        (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).inv := by
  rw [bigSmallEtale_pushforwardCommIso_hom_eq]
  exact mateEquiv_symm_whiskerLeft _ _ _ _

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- `ε_{X,*}` is fully faithful on sheaves of sets. -/
def fppfToBigEtale_pushforwardFullyFaithful (X : T.Spaces) :
    (fppfToBigEtaleMorphism T E h X).pushforward.FullyFaithful := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      exact { preimage := fun f ↦ ObjectProperty.homMk f.hom }

/-- The counit `ε_X⁻¹ε_{X,*}M ⟶ M` is an isomorphism, `ε_{X,*}` being fully faithful. -/
theorem isIso_fppfToBigEtaleMorphism_counit (X : T.Spaces) :
    IsIso (fppfToBigEtaleMorphism T E h X).adj.counit := by
  have := (fppfToBigEtale_pushforwardFullyFaithful T E h X).full
  have := (fppfToBigEtale_pushforwardFullyFaithful T E h X).faithful
  infer_instance

variable {T E h} in
/-- The small square `bigFppfSmallEtale_pushforwardCommIso` is the big square
`bigFppfBigEtale_pushforwardCommIso` pasted with the square `bigSmallEtale_pushforwardCommIso`. -/
theorem bigFppfSmallEtale_pushforwardCommIso_hom_eq_hComp {X Y : T.Spaces} (f : Y ⟶ X) :
    (bigFppfSmallEtale_pushforwardCommIso T E h f).hom =
      (bigFppfBigEtale_pushforwardCommIso T E h f).hom ≫ₕ
        (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      rfl

/-- The canonical base change map `a_X⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_Y⁻¹` for a morphism
`f : Y ⟶ X` of algebraic spaces: the mate of the square `bigFppfSmallEtale_pushforwardCommIso`
across `a_Y⁻¹ ⊣ a_{Y,*}` and `a_X⁻¹ ⊣ a_{X,*}`. -/
def fppfToSmallEtaleBaseChange {X Y : T.Spaces} (f : Y ⟶ X) :
    (E.smallEtaleMorphism (etaleMap T E h f)).pushforward ⋙
        (fppfToSmallEtaleMorphism T E h X).inverseImage ⟶
      (fppfToSmallEtaleMorphism T E h Y).inverseImage ⋙ (bigFppfMorphism T f).pushforward :=
  ((mateEquiv (fppfToSmallEtaleMorphism T E h Y).adj (fppfToSmallEtaleMorphism T E h X).adj).symm
    (bigFppfSmallEtale_pushforwardCommIso T E h f).hom)

/-- The canonical base change map is the mate of the square `bigSmallEtale_pushforwardCommIso` for
`π`, followed by the mate of the big square `bigFppfBigEtale_pushforwardCommIso` for `ε`. -/
theorem fppfToSmallEtaleBaseChange_eq_vComp {X Y : T.Spaces} (f : Y ⟶ X) :
    fppfToSmallEtaleBaseChange T E h f =
      (((mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
          (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj).symm
          (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom) ≫ᵥ
        ((mateEquiv (fppfToBigEtaleMorphism T E h Y).adj (fppfToBigEtaleMorphism T E h X).adj).symm
          (bigFppfBigEtale_pushforwardCommIso T E h f).hom)) := by
  have h1 := mateEquiv_hcomp (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
    (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj (fppfToBigEtaleMorphism T E h Y).adj
    (fppfToBigEtaleMorphism T E h X).adj
    ((mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
          (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj).symm
          (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom)
    ((mateEquiv (fppfToBigEtaleMorphism T E h Y).adj (fppfToBigEtaleMorphism T E h X).adj).symm
          (bigFppfBigEtale_pushforwardCommIso T E h f).hom)
  have e1 := (mateEquiv (fppfToBigEtaleMorphism T E h Y).adj
    (fppfToBigEtaleMorphism T E h X).adj).apply_symm_apply
      (bigFppfBigEtale_pushforwardCommIso T E h f).hom
  have e2 := (mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
    (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj).apply_symm_apply
      (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom
  rw [e1, e2] at h1
  unfold fppfToSmallEtaleBaseChange
  rw [bigFppfSmallEtale_pushforwardCommIso_hom_eq_hComp]
  exact (Equiv.symm_apply_eq _).2 h1.symm

/-- **Proper base change for the big fppf topos.** For a proper morphism `f : Y ⟶ X` of algebraic
spaces, the canonical base change map `a_X⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_Y⁻¹` of functors
from sheaves on the small étale site of `Y` to sheaves on the big fppf site of `X` is an
isomorphism. -/
@[stacks 0DGJ "(1)"]
theorem isIso_fppfToSmallEtaleBaseChange_of_isProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom) :
    IsIso (fppfToSmallEtaleBaseChange T E h f) := by
  have hf' : Space.IsProper E.fppfSite S E.fppf_mem (etaleMap T E h f).hom := by
    cases T with
    | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
        tInitialBounded tIsSite tRepresentative =>
      cases E with
      | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
          eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
        cases h
        exact hf
  have hβ : IsIso ((mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj).symm
      (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom) := by
    rw [BigEtaleSpaceSite.mateEquiv_symm_bigSmallEtale_pushforwardCommIso]
    exact (BigEtaleSpaceSite.bigToSmallEtalePushforwardIsoOfIsProper E (etaleMap T E h f)
      hf').isIso_hom
  have hunit := (isIso_fppfToBigEtale_unit_whiskerLeft_and_isIso_fppfToSmallEtale_unit T E h Y).1
  have hcounit := isIso_fppfToBigEtaleMorphism_counit T E h X
  rw [fppfToSmallEtaleBaseChange_eq_vComp]
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  simp only [TwoSquare.vComp_app]
  have : IsIso ((fppfToBigEtaleMorphism T E h Y).adj.unit.app
      ((E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).inverseImage.obj F)) :=
    NatIso.isIso_app_of_isIso (Functor.whiskerLeft _ (fppfToBigEtaleMorphism T E h Y).adj.unit) F
  have := isIso_mateEquiv_symm_app_of_isIso_unit_counit (fppfToBigEtaleMorphism T E h Y).adj
    (fppfToBigEtaleMorphism T E h X).adj (bigFppfBigEtale_pushforwardCommIso T E h f)
    ((E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).inverseImage.obj F)
  have h₂ : IsIso (((mateEquiv (E.bigToSmallEtaleMorphism (etaleSpace T E h Y)).adj
      (E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj).symm
      (E.bigSmallEtale_pushforwardCommIso (etaleMap T E h f)).hom).app F) :=
    NatIso.isIso_app_of_isIso _ F
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) this

/-- For a proper morphism `f : Y ⟶ X` of algebraic spaces, the isomorphism of functors
`a_X⁻¹ ∘ f_{small,*} ≅ f_{big,fppf,*} ∘ a_Y⁻¹` given by the canonical base change map. -/
def fppfToSmallEtalePushforwardIsoOfIsProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom) :
    (E.smallEtaleMorphism (etaleMap T E h f)).pushforward ⋙
        (fppfToSmallEtaleMorphism T E h X).inverseImage ≅
      (fppfToSmallEtaleMorphism T E h Y).inverseImage ⋙ (bigFppfMorphism T f).pushforward :=
  haveI := isIso_fppfToSmallEtaleBaseChange_of_isProper T E h f hf
  asIso (fppfToSmallEtaleBaseChange T E h f)

end AlgebraicGeometry.BigFppfSpaceSite

end

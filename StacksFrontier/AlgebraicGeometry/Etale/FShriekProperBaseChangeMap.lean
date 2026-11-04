module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition

/-!
# The base-change map of the proper-support direct image

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, and let `F` be an abelian
sheaf on the small étale site of `X`. For an étale test object `V` of `Y` with base change
`V' = V ×_Y Y'`, the scheme `X'_{V'}` is the base change of `X_V` along `V' ⟶ V`, so a section
of `F` over `X_V` pulls back to a section of `p⁻¹F` over `X'_{V'}`. These pullbacks form a map
`f_*F ⟶ g_*f'_*(p⁻¹F)`, whose transpose is the pullback map `g⁻¹f_*F ⟶ f'_*(p⁻¹F)` of
Sites, Section 06UM. Since the support of a pulled-back section lies in the inverse image of the
support, and properness is stable under base change, the map carries `g⁻¹f_!F` into
`f'_!(p⁻¹F)`. This is the map the proof of Stacks 0F55 shows to be an isomorphism.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberBaseChangeArrow` — the comparison `X'_{V'} ⟶ p⁻¹(X_V)` of
  objects of the small étale site of `X'`.
* `AlgebraicGeometry.SmallEtale.directImageBaseChangePushforward` — the map
  `f_*F ⟶ g_*f'_*(p⁻¹F)` given by pulling sections back.
* `AlgebraicGeometry.SmallEtale.directImageBaseChange` — its transpose, the pullback map
  `g⁻¹f_*F ⟶ f'_*(p⁻¹F)`, with `directImageBaseChangeNatTrans` its functoriality in `F`.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChange` — the restriction
  `g⁻¹f_!F ⟶ f'_!(p⁻¹F)`, with `properSupportBaseChangeNatTrans` its functoriality in `F`.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportSections_directImageBaseChangeApp` — pulling back
  preserves the proper-support condition.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChange_comp_arrow` — the restricted map is
  the restriction of the pullback map along the inclusions `f_! ⊆ f_*` and `f'_! ⊆ f'_*`.

## References

* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

section Arrow

/-- For a cartesian square, the comparison of `X'_{V'}`, `V' = V ×_Y Y'`, with the base change
of `X_V` along `p`, as a morphism of the small étale site of `X'`. -/
public def fiberBaseChangeArrow (V : SmallEtale B Y.obj Y.property) :
    baseChange B f' (baseChange B g V) ⟶ (smallEtaleBaseChange B p).obj (baseChange B f V) :=
  baseChangeObjLift B p _ _ (fiberBaseChangeMap B p f' f g sq V)
    (fiberBaseChangeMap_snd B p f' f g sq V)

/-- The comparison arrow lies over the comparison of the two étale base changes. -/
public theorem fiberBaseChangeArrow_proj (V : SmallEtale B Y.obj Y.property) :
    (fiberBaseChangeArrow B p f' f g sq V).hom.left ≫
        baseChangeObjProjection B p (baseChange B f V) =
      fiberBaseChangeMap B p f' f g sq V :=
  baseChangeObjLift_proj B p _ _ _ _

/-- The comparison arrow is natural in the test object. -/
public theorem fiberBaseChangeArrow_naturality {V₁ V : SmallEtale B Y.obj Y.property}
    (a : V₁ ⟶ V) :
    fiberBaseChangeArrow B p f' f g sq V₁ ≫
        (smallEtaleBaseChange B p).map ((smallEtaleBaseChange B f).map a) =
      (smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map a) ≫
        fiberBaseChangeArrow B p f' f g sq V := by
  refine baseChangeObj_hom_ext B p ?_
  show (fiberBaseChangeArrow B p f' f g sq V₁).hom.left ≫
      ((smallEtaleBaseChange B p).map ((smallEtaleBaseChange B f).map a)).hom.left ≫
        baseChangeObjProjection B p (baseChange B f V) =
    ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map a)).hom.left ≫
      (fiberBaseChangeArrow B p f' f g sq V).hom.left ≫
        baseChangeObjProjection B p (baseChange B f V)
  rw [baseChangeObjProjection_naturality, ← Category.assoc, fiberBaseChangeArrow_proj,
    fiberBaseChangeArrow_proj, fiberBaseChangeMap_naturality]

end Arrow

section DirectImage

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- Pulling a section of `F` over `X_V` back to a section of `p⁻¹F` over `X'_{V'}`. -/
public abbrev directImageBaseChangeApp (V : SmallEtale B Y.obj Y.property) :
    F.obj.obj (op (baseChange B f V)) ⟶
      ((abPullback.{u, v} B p).obj F).obj.obj (op (baseChange B f' (baseChange B g V))) :=
  pullbackSectionAlongHom B p AddCommGrpCat.{max (u + 1) v} F _ _
    (fiberBaseChangeArrow B p f' f g sq V)

/-- Pulling sections back commutes with restriction along a morphism of test objects. -/
public theorem directImageBaseChangeApp_naturality {V₁ V : SmallEtale B Y.obj Y.property}
    (a : V₁ ⟶ V) (s : F.obj.obj (op (baseChange B f V))) :
    directImageBaseChangeApp.{u, v} B p f' f g sq F V₁
        (F.obj.map ((smallEtaleBaseChange B f).map a).op s) =
      ((abPullback.{u, v} B p).obj F).obj.map
          ((smallEtaleBaseChange B f').map ((smallEtaleBaseChange B g).map a)).op
        (directImageBaseChangeApp.{u, v} B p f' f g sq F V s) := by
  rw [pullbackSectionAlongHom_map.{u, v}, pullbackSectionAlongHom_restrict.{u, v},
    fiberBaseChangeArrow_naturality]

/-- **Sites, 06UM.** The map `f_*F ⟶ g_*f'_*(p⁻¹F)` of abelian sheaves on the small étale site
of `Y` pulling a section over `X_V` back to `X'_{V'}`. -/
public def directImageBaseChangePushforward :
    directImageSheaf B f F ⟶ (smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property) |>.obj
        (directImageSheaf B f' ((abPullback.{u, v} B p).obj F)) :=
  ⟨{ app := fun V => directImageBaseChangeApp.{u, v} B p f' f g sq F V.unop
     naturality := fun _ _ a => by
       ext s
       exact directImageBaseChangeApp_naturality.{u, v} B p f' f g sq F a.unop s }⟩

/-- The component of `directImageBaseChangePushforward` at `V` is `directImageBaseChangeApp`. -/
@[simp]
public theorem directImageBaseChangePushforward_app (V : SmallEtale B Y.obj Y.property) :
    (directImageBaseChangePushforward.{u, v} B p f' f g sq F).hom.app (op V) =
      directImageBaseChangeApp.{u, v} B p f' f g sq F V :=
  rfl

/-- The map `f_*F ⟶ g_*f'_*(p⁻¹F)` is natural in the abelian sheaf. -/
public theorem directImageBaseChangePushforward_natural
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).map φ ≫
        directImageBaseChangePushforward.{u, v} B p f' f g sq G =
      directImageBaseChangePushforward.{u, v} B p f' f g sq F ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          (((smallEtaleBaseChange B f').sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y'.obj Y'.property)
            (SmallEtale.topology B X'.obj X'.property)).map
            ((abPullback.{u, v} B p).map φ)) := by
  ext V s
  exact pullbackSectionAlongHom_sheafMap.{u, v} B p φ _ _ _ s

/-- Transposing along an adjunction and applying the unit gives back the original map. -/
private theorem unit_comp_map_homEquiv_symm {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B : D} (φ : A ⟶ R.obj B) :
    adj.unit.app A ≫ R.map ((adj.homEquiv A B).symm φ) = φ := by
  simpa using (adj.homEquiv_unit (f := (adj.homEquiv A B).symm φ)).symm

/-- **Sites, 06UM.** The pullback map `g⁻¹f_*F ⟶ f'_*(p⁻¹F)` of the cartesian square: the
transpose of `AlgebraicGeometry.SmallEtale.directImageBaseChangePushforward`. -/
public def directImageBaseChange :
    (abPullback.{u, v} B g).obj (directImageSheaf B f F) ⟶
      directImageSheaf B f' ((abPullback.{u, v} B p).obj F) :=
  (((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).homEquiv _ _).symm
    (directImageBaseChangePushforward.{u, v} B p f' f g sq F)

/-- The pullback map is the transpose of the map pulling sections back. -/
public theorem directImageBaseChange_triangle :
    ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).unit.app (directImageSheaf B f F) ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          (directImageBaseChange.{u, v} B p f' f g sq F) =
      directImageBaseChangePushforward.{u, v} B p f' f g sq F := by
  exact unit_comp_map_homEquiv_symm _ _

/-- **Sites, 06UM.** The pullback map `g⁻¹f_* ⟶ f'_*p⁻¹` of the cartesian square, as a morphism
of functors on abelian sheaves on the small étale site of `X`. -/
public def directImageBaseChangeNatTrans :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property) ⋙
      abPullback.{u, v} B g ⟶
    abPullback.{u, v} B p ⋙
      (smallEtaleBaseChange B f').sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y'.obj Y'.property)
        (SmallEtale.topology B X'.obj X'.property) where
  app F := directImageBaseChange.{u, v} B p f' f g sq F
  naturality F G φ := by
    have hleft := ((smallEtaleBaseChange B g).sheafAdjunctionContinuous
        AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_naturality_left_symm
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)).map φ)
      (directImageBaseChangePushforward.{u, v} B p f' f g sq G)
    have hright := ((smallEtaleBaseChange B g).sheafAdjunctionContinuous
        AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_naturality_right_symm
      (directImageBaseChangePushforward.{u, v} B p f' f g sq F)
      (((smallEtaleBaseChange B f').sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Y'.obj Y'.property)
        (SmallEtale.topology B X'.obj X'.property)).map ((abPullback.{u, v} B p).map φ))
    exact hleft.symm.trans
      ((congrArg _ (directImageBaseChangePushforward_natural.{u, v} B p f' f g sq φ)).trans
        hright)

/-- The component of `directImageBaseChangeNatTrans` at `F` is `directImageBaseChange`. -/
@[simp]
public theorem directImageBaseChangeNatTrans_app :
    (directImageBaseChangeNatTrans.{u, v} B p f' f g sq).app F =
      directImageBaseChange.{u, v} B p f' f g sq F :=
  rfl

end DirectImage

section ProperSupport

variable [LocallyOfFiniteType (B.inclusion.map f)]

/-- **Stacks 0F55**, the first step of the proof: pulling a section with support proper over `V`
back to `X'_{V'}` gives a section with support proper over `V'`, since the support of the
pulled-back section lies in the inverse image of the support, and properness is stable under
base change. -/
public theorem properSupportSections_directImageBaseChangeApp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B Y.obj Y.property) (s : F.obj.obj (op (baseChange B f V)))
    (hs : properSupportSections B f F V s) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    properSupportSections B f' ((abPullback.{u, v} B p).obj F) (baseChange B g V)
      (directImageBaseChangeApp.{u, v} B p f' f g sq F V s) := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  have := hasPullbacks_bigEtaleSite B
  have hfv : LocallyOfFiniteType (B.inclusion.map (fiberProjection B f V)) :=
    locallyOfFiniteType_baseChangeProjection B f V
  have hfv' : LocallyOfFiniteType
      (B.inclusion.map (fiberProjection B f' (baseChange B g V))) :=
    locallyOfFiniteType_baseChangeProjection B f' (baseChange B g V)
  have hsq : IsPullback (fiberBaseChangeScheme B p f' f g sq V)
      (B.inclusion.map (fiberProjection B f' (baseChange B g V)))
      (B.inclusion.map (fiberProjection B f V))
      (B.inclusion.map (fiberProjection B g V)) :=
    (isPullback_fiberBaseChangeMap B p f' f g sq V).map B.inclusion
  have hpre := isProperOver_preimage_baseChange _ _ _ _ hsq
    (zeroOpen B X.obj X.property F (baseChange B f V) s).compl hs
  have hcomp : (SmallEtale.toScheme B X'.obj X'.property).map
        (fiberBaseChangeArrow B p f' f g sq V) ≫
      B.inclusion.map (baseChangeObjProjection B p (baseChange B f V)) =
        fiberBaseChangeScheme B p f' f g sq V :=
    (B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (fiberBaseChangeArrow_proj B p f' f g sq V))
  refine isProperOver_of_le (B.inclusion.map (fiberProjection B f' (baseChange B g V)))
    (fun x hx => ?_) hpre
  have hsub := supportSection_pullbackSectionAlongHom_subset.{u, v} B p F (baseChange B f V)
    (baseChange B f' (baseChange B g V)) (fiberBaseChangeArrow B p f' f g sq V) s hx
  rw [hcomp] at hsub
  exact hsub

variable [LocallyOfFiniteType (B.inclusion.map f')]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The map pulling sections back, restricted to the proper-support sections: a map
`f_!F ⟶ g_*f'_!(p⁻¹F)`. -/
public def properSupportBaseChangePushforward :
    (properSupportFunctor B f).obj F ⟶ (smallEtaleBaseChange B g).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property) |>.obj
        ((properSupportFunctor B f').obj ((abPullback.{u, v} B p).obj F)) :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom
        { toFun := fun s => ⟨directImageBaseChangeApp.{u, v} B p f' f g sq F V.unop s.1,
            properSupportSections_directImageBaseChangeApp.{u, v} B p f' f g sq F V.unop s.1
              s.2⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun s t => Subtype.ext (map_add _ s.1 t.1) }
     naturality := fun _ _ a => by
       ext s
       exact Subtype.ext
         (directImageBaseChangeApp_naturality.{u, v} B p f' f g sq F a.unop s.1) }⟩

/-- The restricted map is the map pulling sections back, read through the inclusions. -/
public theorem properSupportBaseChangePushforward_comp :
    properSupportBaseChangePushforward.{u, v} B p f' f g sq F ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          (fShriekSubsheaf B f' ((abPullback.{u, v} B p).obj F)).val.arrow =
      (fShriekSubsheaf B f F).val.arrow ≫
        directImageBaseChangePushforward.{u, v} B p f' f g sq F :=
  rfl

/-- **Stacks 0F55.** The base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)`: the transpose of the map
pulling proper-support sections back. -/
public def properSupportBaseChange :
    (abPullback.{u, v} B g).obj ((properSupportFunctor B f).obj F) ⟶
      (properSupportFunctor B f').obj ((abPullback.{u, v} B p).obj F) :=
  (((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).homEquiv _ _).symm
    (properSupportBaseChangePushforward.{u, v} B p f' f g sq F)

/-- The base-change map is the transpose of the map pulling proper-support sections back. -/
public theorem properSupportBaseChange_triangle :
    ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).unit.app
          ((properSupportFunctor B f).obj F) ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          (properSupportBaseChange.{u, v} B p f' f g sq F) =
      properSupportBaseChangePushforward.{u, v} B p f' f g sq F := by
  exact unit_comp_map_homEquiv_symm _ _

/-- **Stacks 0F55.** The base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` is the restriction of the
pullback map `g⁻¹f_*F ⟶ f'_*(p⁻¹F)` along the inclusions `f_! ⊆ f_*` and `f'_! ⊆ f'_*`. -/
public theorem properSupportBaseChange_comp_arrow :
    properSupportBaseChange.{u, v} B p f' f g sq F ≫
        (fShriekSubsheaf B f' ((abPullback.{u, v} B p).obj F)).val.arrow =
      (abPullback.{u, v} B g).map (fShriekSubsheaf B f F).val.arrow ≫
        directImageBaseChange.{u, v} B p f' f g sq F := by
  exact (((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_naturality_right_square _ _ _ _
      (properSupportBaseChangePushforward_comp.{u, v} B p f' f g sq F)).symm

/-- **Stacks 0F55.** The base-change map `g⁻¹f_! ⟶ f'_!p⁻¹` as a morphism of functors on
abelian sheaves on the small étale site of `X`. -/
public def properSupportBaseChangeNatTrans :
    properSupportFunctor B f ⋙ abPullback.{u, v} B g ⟶
      abPullback.{u, v} B p ⋙ properSupportFunctor B f' where
  app F := properSupportBaseChange.{u, v} B p f' f g sq F
  naturality F G φ := by
    dsimp only [Functor.comp_map]
    apply (cancel_mono (properSupportSheafInclusion B f' ((abPullback.{u, v} B p).obj G))).1
    have h1 := properSupportBaseChange_comp_arrow.{u, v} B p f' f g sq G
    have h2 := properSupportBaseChange_comp_arrow.{u, v} B p f' f g sq F
    have h3 : (properSupportFunctor B f').map ((abPullback.{u, v} B p).map φ) ≫
          (fShriekSubsheaf B f' ((abPullback.{u, v} B p).obj G)).val.arrow =
        (fShriekSubsheaf B f' ((abPullback.{u, v} B p).obj F)).val.arrow ≫
          ((smallEtaleBaseChange B f').sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y'.obj Y'.property)
            (SmallEtale.topology B X'.obj X'.property)).map ((abPullback.{u, v} B p).map φ) :=
      (fShriekMap B f' _ _ _).property
    have h4 : (properSupportFunctor B f).map φ ≫ (fShriekSubsheaf B f G).val.arrow =
        (fShriekSubsheaf B f F).val.arrow ≫
          ((smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).map φ :=
      (fShriekMap B f _ _ φ).property
    have h5 := (directImageBaseChangeNatTrans.{u, v} B p f' f g sq).naturality φ
    dsimp only [Functor.comp_map, directImageBaseChangeNatTrans_app] at h5
    simp only [fShriekSubsheaf_arrow] at h1 h2 h3 h4
    let gP := abPullback.{u, v} B g
    exact (Category.assoc _ _ _).trans <|
      (congrArg (gP.map ((properSupportFunctor B f).map φ) ≫ ·) h1).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ directImageBaseChange.{u, v} B p f' f g sq G)
        ((gP.map_comp _ _).symm.trans ((congrArg gP.map h4).trans (gP.map_comp _ _)))).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (gP.map (properSupportSheafInclusion B f F) ≫ ·) h5).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ ((smallEtaleBaseChange B f').sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (SmallEtale.topology B Y'.obj Y'.property)
          (SmallEtale.topology B X'.obj X'.property)).map ((abPullback.{u, v} B p).map φ))
        h2.symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (properSupportBaseChange.{u, v} B p f' f g sq F ≫ ·) h3.symm).trans <|
      (Category.assoc _ _ _).symm

/-- The component of `properSupportBaseChangeNatTrans` at `F` is `properSupportBaseChange`. -/
@[simp]
public theorem properSupportBaseChangeNatTrans_app :
    (properSupportBaseChangeNatTrans.{u, v} B p f' f g sq).app F =
      properSupportBaseChange.{u, v} B p f' f g sq F :=
  rfl

end ProperSupport

end AlgebraicGeometry.SmallEtale

end

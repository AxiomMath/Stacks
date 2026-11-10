module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.RestrictionAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.SectionExtension
import all StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.RestrictionAdjunction
import all StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusion.SectionExtension

/-!
# Extension by zero from an open subscheme into the proper-support direct image

Let `f : X ⟶ Y` be a separated morphism locally of finite type in a big étale site and let
`j : X' ⟶ X` be an open immersion in that site, and let `F'` be the restriction to `X'` of an
abelian sheaf `F` on the small étale site of `X`. The extensions by zero of sections of
`(j ≫ f)_! F'` assemble into a monomorphism `(j ≫ f)_! F' ⟶ f_! F` of abelian sheaves on
the small étale site of `Y`, characterised sectionwise by two equations: restricting the
extended section back to the open piece returns the original section, and the support of the
extended section is the image of the support of the original one.

## Main results

* `AlgebraicGeometry.SmallEtale.openInclusionShriekMap`: the canonical monomorphism of
  proper-support direct images, bundled with its two characterising equations.

## References

* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- A monomorphism of abelian sheaves is injective on sections. -/
private theorem sheaf_hom_app_injective_of_mono {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{v}} (m : P ⟶ Q) [Mono m]
    (V : Cᵒᵖ) : Function.Injective (m.hom.app V).hom := by
  have : Mono ((sheafToPresheaf J AddCommGrpCat.{v}).map m) := Functor.map_mono _ _
  exact (AddCommGrpCat.mono_iff_injective (((sheafToPresheaf J _).map m).app V)).mp inferInstance

/-- Restricting a section to the open piece and comparing with `openRestrictionIso` is the unit
of the base-change adjunction. -/
private theorem openRestrictionIso_restrict_eq_unit
    (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) (s : F.obj.obj (op W)) :
    (((openRestrictionIso B j).app F).hom.hom.app (op ((smallEtaleBaseChange B j).obj W)))
        (F.obj.map (openBaseChangeMap B j W).op s) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s :=
  openRestrictionIso_unit_app B j F W s

private noncomputable def openInclusionShriekSection
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map (j ≫ f))]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (a : ((SmallEtale.fShriekSubsheaf B (j ≫ f)
      (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F)).val.obj.left.obj.obj (op V))) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
    let G := (SmallEtale.fShriekSubsheaf B f F).val
    let sOld := G'.arrow.hom.app (op V) a
    let _hsOld : SmallEtale.properSupportSections B (j ≫ f) F' V sOld := by
      apply ((SmallEtale.fShriekSubsheaf B (j ≫ f) F').property V sOld).mp
      exact ⟨a, by rfl⟩
    let W := (smallEtaleBaseChange B f).obj V
    let W' := (smallEtaleBaseChange B j).obj W
    let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
    let s'W := F'.obj.map (e.hom.app V).op sOld
    {s : G.obj.left.obj.obj (op V) //
      SmallEtale.properSupportSections B f F V (G.arrow.hom.app (op V) s) ∧
      F'.obj.map (e.hom.app V).op sOld =
        (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W)
          (G.arrow.hom.app (op V) s) ∧
      SmallEtale.supportSection B X.obj X.property F W
          (G.arrow.hom.app (op V) s) =
        (B.inclusion.map (pullback.fst W.obj.hom j)).base ''
          SmallEtale.supportSection B X'.obj X'.property F' W' s'W} := by
  classical
  letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let sOld := G'.arrow.hom.app (op V) a
  have hsOld : SmallEtale.properSupportSections B (j ≫ f) F' V sOld :=
    (SmallEtale.fShriekSubsheaf B (j ≫ f) F').property V sOld |>.mp ⟨a, rfl⟩
  have hE := openInclusionExtendSection_exists B j f F V sOld hsOld
  let E := Classical.choose hE
  have hEprop := Classical.choose_spec hE
  have hmem : E ∈ Set.range (G.arrow.hom.app (op V)) :=
    (SmallEtale.fShriekSubsheaf B f F).property V E |>.mpr hEprop.2.1
  let b := Classical.choose hmem
  have hb : G.arrow.hom.app (op V) b = E := Classical.choose_spec hmem
  refine ⟨b, ?_, ?_, ?_⟩ <;> rw [hb]
  exacts [hEprop.2.1, hEprop.2.2, hEprop.1]

private theorem openInclusionShriekSection_zero
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map (j ≫ f))]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property) :
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
    (openInclusionShriekSection B j f F V
      (0 : G'.obj.left.obj.obj (op V))).val = 0 := by
  classical
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let W := (smallEtaleBaseChange B f).obj V
  let W' := (smallEtaleBaseChange B j).obj W
  let U' := (postcompose B j).obj W'
  let φ := openBaseChangeMap B j W
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  let c := openInclusionShriekSection B j f F V (0 : G'.obj.left.obj.obj (op V))
  let s : F.obj.obj (op W) := by
    change F.obj.obj (op ((smallEtaleBaseChange B f).obj V))
    exact G.arrow.hom.app (op V) c.val
  let eOpen := (openRestrictionIso B j).app F
  have hunit : F'.obj.map (e.hom.app V).op
      (G'.arrow.hom.app (op V) (0 : G'.obj.left.obj.obj (op V))) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s :=
    c.property.2.1
  have hmap0 : F'.obj.map (e.hom.app V).op
      (G'.arrow.hom.app (op V) (0 : G'.obj.left.obj.obj (op V))) = 0 := by
    rw [(G'.arrow.hom.app (op V)).hom.map_zero]
    exact (F'.obj.map (e.hom.app V).op).hom.map_zero
  have hunit0 : (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s = 0 := by
    rw [← hunit, hmap0]
    rfl
  let : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map φ) :=
    openBaseChangeMap_isOpenImmersion B j W
  have hrestr0 : F.obj.map φ.op s = 0 := by
    have hinj : Function.Injective
      ((eOpen.hom.hom.app (op W')).hom) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hinj
    rw [openRestrictionIso_restrict_eq_unit B j F W s, hunit0]
    exact ((eOpen.hom.hom.app (op W')).hom.map_zero).symm
  have hsupport : SmallEtale.supportSection B X.obj X.property F W s ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map φ).base := by
    exact c.property.2.2.subset.trans (Set.image_subset_range _ _)
  have hzero := restriction_eq_zero_of_support_subset B X.obj X.property F W U' φ
    s hsupport hrestr0
  change c.val = 0
  apply sheaf_hom_app_injective_of_mono G.arrow
  have hzero' : (G.arrow.hom.app (op V)).hom c.val = 0 := hzero
  simpa using hzero'

private theorem openInclusionShriekSection_add
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map (j ≫ f))]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (a b : (SmallEtale.fShriekSubsheaf B (j ≫ f)
      (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).obj F)).val.obj.left.obj.obj (op V)) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let _G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
    let _G := (SmallEtale.fShriekSubsheaf B f F).val
    (openInclusionShriekSection B j f F V (a + b)).val =
      (openInclusionShriekSection B j f F V a).val +
        (openInclusionShriekSection B j f F V b).val := by
  classical
  let : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let W := (smallEtaleBaseChange B f).obj V
  let W' := (smallEtaleBaseChange B j).obj W
  let U' := (postcompose B j).obj W'
  let φ := openBaseChangeMap B j W
  let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
  let eOpen := (openRestrictionIso B j).app F
  let ea := openInclusionShriekSection B j f F V a
  let eb := openInclusionShriekSection B j f F V b
  let eab := openInclusionShriekSection B j f F V (a + b)
  let sa := (G.arrow.hom.app (op V)).hom ea.val
  let sb := (G.arrow.hom.app (op V)).hom eb.val
  let sab := (G.arrow.hom.app (op V)).hom eab.val
  have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map φ) :=
    openBaseChangeMap_isOpenImmersion B j W
  have hsupport (c : G'.obj.left.obj.obj (op V)) :
      SmallEtale.supportSection B X.obj X.property F W
          ((G.arrow.hom.app (op V)).hom (openInclusionShriekSection B j f F V c).val) ⊆
        Set.range ((SmallEtale.toScheme B X.obj X.property).map φ).base := by
    exact (openInclusionShriekSection B j f F V c).property.2.2.subset.trans
      (Set.image_subset_range _ _)
  have hsupport_sum :
      SmallEtale.supportSection B X.obj X.property F W (sa + sb) ⊆
        Set.range ((SmallEtale.toScheme B X.obj X.property).map φ).base :=
    (SmallEtale.supportSection_add_subset B X.obj X.property F W sa sb).trans
      (Set.union_subset (hsupport a) (hsupport b))
  have hR (c : G'.obj.left.obj.obj (op V)) :
      (eOpen.hom.hom.app (op W')) (F.obj.map φ.op
          ((G.arrow.hom.app (op V)).hom (openInclusionShriekSection B j f F V c).val)) =
        F'.obj.map (e.hom.app V).op (G'.arrow.hom.app (op V) c) := by
    have hUnit := (openInclusionShriekSection B j f F V c).property.2.1
    exact (openRestrictionIso_restrict_eq_unit B j F W _).trans hUnit.symm
  have hR_a := hR a
  have hR_b := hR b
  have hR_ab := hR (a + b)
  have hrestr : F.obj.map φ.op sab = F.obj.map φ.op (sa + sb) := by
    have hinj : Function.Injective ((eOpen.hom.hom.app (op W')).hom) :=
      (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    apply hinj
    calc
      _ = F'.obj.map (e.hom.app V).op
          (G'.arrow.hom.app (op V) (a + b)) := hR_ab
      _ = (F'.obj.map (e.hom.app V).op).hom
          ((G'.arrow.hom.app (op V)).hom a +
            (G'.arrow.hom.app (op V)).hom b) := by
        change (F'.obj.map (e.hom.app V).op).hom
          ((G'.arrow.hom.app (op V)).hom (a + b)) = _
        rw [(G'.arrow.hom.app (op V)).hom.map_add]
      _ = (F'.obj.map (e.hom.app V).op).hom
          ((G'.arrow.hom.app (op V)).hom a) +
          (F'.obj.map (e.hom.app V).op).hom ((G'.arrow.hom.app (op V)).hom b) :=
        (F'.obj.map (e.hom.app V).op).hom.map_add _ _
      _ = (eOpen.hom.hom.app (op W')) (F.obj.map φ.op sa) +
          (eOpen.hom.hom.app (op W')) (F.obj.map φ.op sb) := by rw [hR_a, hR_b]
      _ = (eOpen.hom.hom.app (op W')) (F.obj.map φ.op (sa + sb)) :=
        (((eOpen.hom.hom.app (op W')).hom.comp (F.obj.map φ.op).hom).map_add sa sb).symm
  have hsection := section_eq_of_restrict_eq B X.obj X.property F W U' φ
    sab (sa + sb) (hsupport (a + b)) hsupport_sum hrestr
  apply sheaf_hom_app_injective_of_mono G.arrow
  calc
    _ = (G.arrow.hom.app (op V)).hom ea.val +
        (G.arrow.hom.app (op V)).hom eb.val := hsection
    _ = (G.arrow.hom.app (op V)).hom (ea.val + eb.val) :=
      ((G.arrow.hom.app (op V)).hom.map_add ea.val eb.val).symm

private noncomputable def openInclusionShriekMapConstruction
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
    let G := (SmallEtale.fShriekSubsheaf B f F).val
    {α : G'.obj.left ⟶ G.obj.left //
      Mono α ∧
      ∀ (V : SmallEtale B Y.obj Y.property) (a : G'.obj.left.obj.obj (op V)),
        let W := (smallEtaleBaseChange B f).obj V
        let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
        let s := G.arrow.hom.app (op V) (α.hom.app (op V) a)
        let s' := G'.arrow.hom.app (op V) a
        let s'W := F'.obj.map (e.hom.app V).op s'
        (F'.obj.map (e.hom.app V).op s' =
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s) ∧
        (SmallEtale.supportSection B X.obj X.property F W s =
          (B.inclusion.map (pullback.fst W.obj.hom j)).base ''
            SmallEtale.supportSection B X'.obj X'.property F'
              ((smallEtaleBaseChange B j).obj W) s'W)} := by
  classical
  letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
    infer_instance
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
  let G := (SmallEtale.fShriekSubsheaf B f F).val
  let η : G'.obj.left.obj ⟶ G.obj.left.obj := {
    app := fun V => AddCommGrpCat.ofHom {
      toFun a := (openInclusionShriekSection B j f F V.unop a).val
      map_zero' := openInclusionShriekSection_zero B j f F V.unop
      map_add' := openInclusionShriekSection_add B j f F V.unop }
    naturality := by
      intro V₁ V₂ g
      ext a
      let Vlarge := V₁.unop
      let Vsmall := V₂.unop
      let aSmall := (G'.obj.left.obj.map g).hom a
      let cLarge := openInclusionShriekSection B j f F Vlarge a
      let cSmall := openInclusionShriekSection B j f F Vsmall aSmall
      change cSmall.val = (G.obj.left.obj.map g).hom cLarge.val
      let Wlarge := (smallEtaleBaseChange B f).obj Vlarge
      let Wsmall := (smallEtaleBaseChange B f).obj Vsmall
      let gW := (smallEtaleBaseChange B f).map g.unop
      apply sheaf_hom_app_injective_of_mono G.arrow
      have hGnat :
          (G.arrow.hom.app V₂).hom
              ((G.obj.left.obj.map g).hom cLarge.val) =
            (F.obj.map gW.op).hom ((G.arrow.hom.app V₁).hom cLarge.val) := by
        exact congrArg (fun z => z.hom cLarge.val) (G.arrow.hom.naturality g)
      rw [hGnat]
      let T := SmallEtale.toScheme B X.obj X.property
      let φLarge := openBaseChangeMap B j Wlarge
      let φSmall := openBaseChangeMap B j Wsmall
      let sLarge := (G.arrow.hom.app V₁).hom cLarge.val
      let sSmall := (G.arrow.hom.app V₂).hom cSmall.val
      let sRestr : F.obj.obj (op Wsmall) := (F.obj.map gW.op).hom sLarge
      have hSupportSmall :
          SmallEtale.supportSection B X.obj X.property F Wsmall sSmall ⊆
            Set.range (T.map φSmall).base := by
        exact cSmall.property.2.2.subset.trans (Set.image_subset_range _ _)
      have hOver := Over.w ((SmallEtale.inclusion B X.obj X.property).map gW)
      have hcomm : T.map gW ≫ B.inclusion.map Wlarge.obj.hom =
          B.inclusion.map Wsmall.obj.hom := by
        change B.inclusion.map
            (((SmallEtale.inclusion B X.obj X.property).map gW).left ≫
              Wlarge.obj.hom) = B.inclusion.map Wsmall.obj.hom
        rw [B.inclusion.map_comp]
        exact congrArg B.inclusion.map hOver
      have hpoint (x : T.obj Wsmall) :
          (B.inclusion.map Wlarge.obj.hom).base ((T.map gW).base x) =
            (B.inclusion.map Wsmall.obj.hom).base x := by
        have h := congrArg (fun q : Scheme.Hom _ _ => q.base x) hcomm
        rw [Scheme.Hom.comp_base, TopCat.coe_comp] at h
        exact h
      have hSupportRestr :
          SmallEtale.supportSection B X.obj X.property F Wsmall sRestr ⊆
            Set.range (T.map φSmall).base := by
        have hsub := supportSection_restrict_subset B X.obj X.property F
          Wlarge Wsmall gW sLarge
        intro x hx
        have hx' := hsub hx
        have hlarge : (T.map gW).base x ∈ Set.range (T.map φLarge).base := by
          change (T.map gW).base x ∈
            SmallEtale.supportSection B X.obj X.property F Wlarge
              ((G.arrow.hom.app V₁) cLarge.val) at hx'
          rw [cLarge.property.2.2] at hx'
          change (T.map gW).base x ∈ Set.range
            (B.inclusion.map (pullback.fst Wlarge.obj.hom j)).base
          rcases hx' with ⟨y, hy, hxy⟩
          exact ⟨y, hxy⟩
        change (T.map gW).base x ∈
          Set.range (T.map (openBaseChangeMap B j Wlarge)).base at hlarge
        rw [openBaseChangeMap_range B j Wlarge] at hlarge
        have hbase : (B.inclusion.map Wsmall.obj.hom).base x ∈
            Set.range (B.inclusion.map j).base := by
          rw [← hpoint x]
          exact hlarge
        change x ∈ Set.range (T.map (openBaseChangeMap B j Wsmall)).base
        rw [openBaseChangeMap_range B j Wsmall]
        exact hbase
      let D := smallEtaleBaseChange B (j ≫ f)
      let I := smallEtaleBaseChange B f ⋙ smallEtaleBaseChange B j
      let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
      have hOldRestr :
          (G'.arrow.hom.app (op Vsmall)).hom aSmall =
            (F'.obj.map (D.map g.unop).op).hom
              ((G'.arrow.hom.app (op Vlarge)).hom a) := by
        exact congrArg (fun z => z.hom a) (G'.arrow.hom.naturality g)
      have hSource : F'.obj.map (e.hom.app Vsmall).op
            ((G'.arrow.hom.app (op Vsmall)).hom aSmall) =
          F'.obj.map ((smallEtaleBaseChange B j).map gW).op
            (F'.obj.map (e.hom.app Vlarge).op
              ((G'.arrow.hom.app (op Vlarge)).hom a)) := by
        calc
          _ = F'.obj.map (e.hom.app Vsmall).op
              ((F'.obj.map (D.map g.unop).op).hom
                ((G'.arrow.hom.app (op Vlarge)).hom a)) := by rw [hOldRestr]
          _ = F'.obj.map ((smallEtaleBaseChange B j).map gW).op
              (F'.obj.map (e.hom.app Vlarge).op
                ((G'.arrow.hom.app (op Vlarge)).hom a)) := by
            have h := congrArg
              (fun k => (F'.obj.map k.op).hom
                ((G'.arrow.hom.app (op Vlarge)).hom a)) (e.hom.naturality g.unop)
            simp only [op_comp, Functor.map_comp] at h
            change (F'.obj.map ((smallEtaleBaseChange B j).map gW).op).hom
                ((F'.obj.map (e.hom.app Vlarge).op)
                  ((G'.arrow.hom.app (op Vlarge)).hom a)) =
              (F'.obj.map (e.hom.app Vsmall).op).hom
                ((F'.obj.map (D.map g.unop).op).hom
                  ((G'.arrow.hom.app (op Vlarge)).hom a)) at h
            exact h.symm
      let adj := (smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)
      have hUnitNat :
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op Wsmall) sRestr =
            (F'.obj.map ((smallEtaleBaseChange B j).map gW).op).hom
              ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
                (SmallEtale.topology B X.obj X.property)
                (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
                  (op Wlarge) sLarge) := by
        have h := congrArg (fun z => z.hom sLarge)
          ((adj.unit.app F).hom.naturality gW.op)
        dsimp [Functor.sheafPushforwardContinuous] at h
        change (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op Wsmall) sRestr =
          (F'.obj.map ((smallEtaleBaseChange B j).map gW).op).hom
            ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
                (op Wlarge) sLarge) at h
        exact h
      have hUnits :
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op Wsmall) sSmall =
            (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
                (op Wsmall) sRestr := by
        rw [← cSmall.property.2.1, hSource, cLarge.property.2.1]
        exact hUnitNat.symm
      let eOpen := (openRestrictionIso B j).app F
      have hrestr : F.obj.map φSmall.op sSmall = F.obj.map φSmall.op sRestr := by
        have hinj : Function.Injective ((eOpen.hom.hom.app
            (op ((smallEtaleBaseChange B j).obj Wsmall))).hom) :=
          (AddCommGrpCat.mono_iff_injective _).mp inferInstance
        exact hinj ((openRestrictionIso_restrict_eq_unit B j F Wsmall sSmall).trans
          (hUnits.trans (openRestrictionIso_restrict_eq_unit B j F Wsmall sRestr).symm))
      let : IsOpenImmersion (T.map φSmall) :=
        openBaseChangeMap_isOpenImmersion B j Wsmall
      let Usmall' := (postcompose B j).obj ((smallEtaleBaseChange B j).obj Wsmall)
      exact section_eq_of_restrict_eq B X.obj X.property F Wsmall
        Usmall' φSmall sSmall sRestr hSupportSmall hSupportRestr hrestr
    }
  let α : G'.obj.left ⟶ G.obj.left := Sheaf.homEquiv.symm η
  have hmono : Mono α := by
    have hη : Mono η := by
      rw [NatTrans.mono_iff_mono_app]
      intro V
      apply (AddCommGrpCat.mono_iff_injective _).2
      intro a b hab
      let W := (smallEtaleBaseChange B f).obj V.unop
      let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
      let ea := openInclusionShriekSection B j f F V.unop a
      let eb := openInclusionShriekSection B j f F V.unop b
      have habG : G.arrow.hom.app V (ea.val) = G.arrow.hom.app V (eb.val) :=
        congrArg (fun z => G.arrow.hom.app V z) hab
      have hunit : F'.obj.map (e.hom.app V.unop).op
          (G'.arrow.hom.app V a) =
          F'.obj.map (e.hom.app V.unop).op (G'.arrow.hom.app V b) := by
        rw [ea.property.2.1, habG, ← eb.property.2.1]
      have : IsIso (F'.obj.map (e.hom.app V.unop).op) := inferInstance
      have hinj : Function.Injective
          ((F'.obj.map (e.hom.app V.unop).op).hom) :=
        (AddCommGrpCat.mono_iff_injective _).mp inferInstance
      have himage : G'.arrow.hom.app V a = G'.arrow.hom.app V b :=
        hinj hunit
      exact sheaf_hom_app_injective_of_mono G'.arrow V himage
    exact (sheafToPresheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{v}).mono_of_mono_map hη
  refine ⟨α, hmono, ?_⟩
  intro V a
  let b := openInclusionShriekSection B j f F V a
  have hs : G.arrow.hom.app (op V) (α.hom.app (op V) a) =
      G.arrow.hom.app (op V) b.val := rfl
  dsimp only
  rw [hs]
  exact ⟨b.property.2.1, b.property.2.2⟩

/-- The canonical injection from the proper-support direct image on an open
subscheme, with its sectionwise extension-by-zero characterization. -/
@[stacks 0F53 "open_inclusion_mono"]
public noncomputable def openInclusionShriekMap
    (B : BigEtaleSite.{u}) {X' X Y : B.Scheme}
    (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) := by
      change LocallyOfFiniteType (B.inclusion.map j ≫ B.inclusion.map f)
      infer_instance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let G' := (SmallEtale.fShriekSubsheaf B (j ≫ f) F').val
    let G := (SmallEtale.fShriekSubsheaf B f F).val
    {α : G'.obj.left ⟶ G.obj.left //
      Mono α ∧
      ∀ (V : SmallEtale B Y.obj Y.property) (a : G'.obj.left.obj.obj (op V)),
        let W := (smallEtaleBaseChange B f).obj V
        let e := (smallEtaleBaseChange_compIso B X' X Y j f).val
        let s := G.arrow.hom.app (op V) (α.hom.app (op V) a)
        let s' := G'.arrow.hom.app (op V) a
        let s'W := F'.obj.map (e.hom.app V).op s'
        (F'.obj.map (e.hom.app V).op s' =
          (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) s) ∧
        (SmallEtale.supportSection B X.obj X.property F W s =
          (B.inclusion.map (pullback.fst W.obj.hom j)).base ''
            SmallEtale.supportSection B X'.obj X'.property F'
              ((smallEtaleBaseChange B j).obj W) s'W)} :=
  Classical.choice (by exact ⟨openInclusionShriekMapConstruction B j f F⟩)

end AlgebraicGeometry.SmallEtale

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u v
namespace AlgebraicGeometry.SmallEtale

/-- Post-composition with an open immersion `j : X' ⟶ X`, as a functor from the small étale
site of `X'` to the small étale site of `X`. -/
private noncomputable def postcomposeOpen (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    SmallEtale B X'.obj X'.property ⥤ SmallEtale B X.obj X.property :=
  smallEtalePostcompose B X.obj X.property (openSiteObject B j)

end AlgebraicGeometry.SmallEtale
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u v
namespace AlgebraicGeometry.SmallEtale

private theorem postcomposeOpen_incl (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] :
    postcomposeOpen B j ⋙ SmallEtale.inclusion B X.obj X.property =
      SmallEtale.inclusion B X'.obj X'.property ⋙ Over.map j := rfl

end AlgebraicGeometry.SmallEtale
end

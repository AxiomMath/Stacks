module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.RelativelyPerfectDiagram

/-!
# The strict cocone and its colimit property

The scalar diagram, cone data on a strictified diagram, the strict cocone, and the criterion
that a cocone of categories over a filtered index category is a colimit when it is so on
objects and arrows.

This is part 9 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

namespace ScalarDiagram

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Bicategory

attribute [local instance] HasDerivedCategory.standard

universe uRing uModule

/-- Total derived extension of scalars along a ring map, as a functor between the derived
categories of modules. -/
abbrev Extension {Source Target : Type uRing} [CommRing Source] [CommRing Target]
    (ringMap : Source →+* Target) :=
  (totalDerivedExtensionScalars.{uRing, uRing, uModule} ringMap).functor

/-- Composition and unit isomorphisms for derived extension of scalars satisfying the
associativity and unit laws of a pseudofunctor. -/
structure Coherence where
  /-- Derived extension along `first` and then `second` is derived extension along
  `second.comp first`. -/
  composition : ∀ {Source Middle Target : Type uRing}
    [CommRing Source] [CommRing Middle] [CommRing Target]
    (first : Source →+* Middle) (second : Middle →+* Target),
    Extension.{uRing, uModule} first ⋙ Extension second ≅ Extension (second.comp first)
  /-- The identity functor is derived extension along the identity ring map. -/
  unit : ∀ (Ring : Type uRing) [CommRing Ring],
    𝟭 (DerivedCategory (ModuleCat.{max uRing uModule} Ring)) ≅ Extension (RingHom.id Ring)
  /-- `composition` is associative. -/
  assoc : ∀ {Source Middle Target Last : Type uRing}
    [CommRing Source] [CommRing Middle] [CommRing Target] [CommRing Last]
    (first : Source →+* Middle) (second : Middle →+* Target) (third : Target →+* Last)
    (object : DerivedCategory (ModuleCat.{max uRing uModule} Source)),
    (Extension third).map ((composition first second).hom.app object) ≫
        (composition (second.comp first) third).hom.app object =
      (composition second third).hom.app ((Extension first).obj object) ≫
        (composition first (third.comp second)).hom.app object
  /-- The unit law for `unit` at the source ring. -/
  unit_left : ∀ {Source Target : Type uRing} [CommRing Source] [CommRing Target]
    (ringMap : Source →+* Target)
    (object : DerivedCategory (ModuleCat.{max uRing uModule} Source)),
    (Extension ringMap).map ((unit Source).hom.app object) ≫
      (composition (RingHom.id Source) ringMap).hom.app object = 𝟙 _
  /-- The unit law for `unit` at the target ring. -/
  unit_right : ∀ {Source Target : Type uRing} [CommRing Source] [CommRing Target]
    (ringMap : Source →+* Target)
    (object : DerivedCategory (ModuleCat.{max uRing uModule} Source)),
    (unit Target).hom.app ((Extension ringMap).obj object) ≫
      (composition ringMap (RingHom.id Target)).hom.app object = 𝟙 _

/-- The pseudofunctor on commutative rings sending a ring to the derived category of its modules
and a ring map to derived extension of scalars, with the coherence isomorphisms of `data`. -/
def pseudofunctor (data : Coherence.{uRing, uModule}) :
    LocallyDiscrete CommRingCat.{uRing} ⥤ᵖ
      Cat.{max uRing uModule + 1, max uRing uModule + 1} where
  obj ring := Cat.of (DerivedCategory (ModuleCat.{max uRing uModule} ring.as))
  map ringMap := (Extension.{uRing, uModule} ringMap.as.hom).toCatHom
  map₂ equality := eqToHom (congrArg
    (fun ringMap ↦ (Extension.{uRing, uModule} ringMap.as.hom).toCatHom)
    (LocallyDiscrete.eq_of_hom equality))
  mapId ring := Cat.Hom.isoMk (data.unit ring.as).symm
  mapComp first second := Cat.Hom.isoMk
    (data.composition first.as.hom second.as.hom).symm
  map₂_whisker_left {source middle target} ringMap {first second} equality := by
    cases LocallyDiscrete.eq_of_hom equality
    have identity : equality = 𝟙 _ := Subsingleton.elim _ _
    subst equality
    simp only [LocallyDiscrete.comp_as, CommRingCat.hom_comp, eqToHom_refl, Cat.of_α,
      Functor.toCatHom_toFunctor, Cat.Hom.isoMk_hom, Iso.symm_hom, whiskerLeft_id,
      Cat.Hom.isoMk_inv, Iso.symm_inv, Category.id_comp]
    apply Cat.Hom₂.ext
    simp
  map₂_whisker_right {source middle target} {first second} equality ringMap := by
    cases LocallyDiscrete.eq_of_hom equality
    have identity : equality = 𝟙 _ := Subsingleton.elim _ _
    subst equality
    simp only [LocallyDiscrete.comp_as, CommRingCat.hom_comp, eqToHom_refl, Cat.of_α,
      Functor.toCatHom_toFunctor, Cat.Hom.isoMk_hom, Iso.symm_hom, id_whiskerRight,
      Cat.Hom.isoMk_inv, Iso.symm_inv, Category.id_comp]
    apply Cat.Hom₂.ext
    simp
  map₂_associator first second third := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    dsimp
    apply (cancel_epi
      ((Extension third.as.hom).map
          ((data.composition first.as.hom second.as.hom).hom.app object) ≫
        (data.composition (second.as.hom.comp first.as.hom) third.as.hom).hom.app object)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    exact data.assoc first.as.hom second.as.hom third.as.hom object
  map₂_left_unitor ringMap := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    dsimp
    apply (cancel_epi
      ((Extension ringMap.as.hom).map ((data.unit _).hom.app object) ≫
        (data.composition (RingHom.id _) ringMap.as.hom).hom.app object)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
    exact data.unit_left ringMap.as.hom object
  map₂_right_unitor ringMap := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext object
    dsimp
    apply (cancel_epi
      ((data.unit _).hom.app ((Extension ringMap.as.hom).obj object) ≫
        (data.composition ringMap.as.hom (RingHom.id _)).hom.app object)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    exact data.unit_right ringMap.as.hom object

end ScalarDiagram

namespace Strictification

open CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe uIndex vIndex uObj vHom uTarget

variable {Index : Type uIndex} [Category.{vIndex} Index]
variable (diagram : LocallyDiscrete Index ⥤ᵖ Cat.{vHom, uObj})

/-- A pseudonatural cocone over `diagram` with apex `Target`: a functor from the category at each
stage to `Target`, with isomorphisms comparing them along the transition functors, compatible
with the composition isomorphisms of `diagram`. -/
structure ConeData (Target : Type uTarget) [Category.{vHom} Target] where
  /-- The functor from the category of `diagram` at a stage to `Target`. -/
  leg : ∀ stage : Index, diagram.obj ⟨stage⟩ ⥤ Target
  /-- The transition functor along an arrow followed by the leg at its target is isomorphic to
  the leg at its source. -/
  comparison : ∀ {source target : Index} (arrow : source ⟶ target),
    (diagram.map arrow.toLoc).toFunctor ⋙ leg target ≅ leg source
  /-- `comparison` is compatible with the composition isomorphisms of `diagram`. -/
  comp : ∀ {source middle target : Index} (first : source ⟶ middle) (second : middle ⟶ target)
    (object : diagram.obj ⟨source⟩),
    (leg target).map ((diagram.mapComp first.toLoc second.toLoc).hom.toNatTrans.app object) ≫
        (comparison second).hom.app ((diagram.map first.toLoc).toFunctor.obj object) ≫
        (comparison first).hom.app object =
      (comparison (first ≫ second)).hom.app object

variable {Target : Type uTarget} [Category.{vHom} Target] (cone : ConeData diagram Target)

/-- The image in `Target` of an object of `diagram` at some stage under the leg of `cone`. -/
abbrev limitEvaluationObj (object : ULift.{vIndex} (Σ stage : Index, diagram.obj ⟨stage⟩)) :
    Target := (cone.leg object.down.1).obj object.down.2

/-- The category of pairs of a stage and an object of `diagram` there, whose morphisms are those
of `Target` between their images under the legs of `cone`. -/
abbrev LimitStage := InducedCategory Target (limitEvaluationObj diagram cone)

/-- The fully faithful functor from `LimitStage diagram cone` to `Target`. -/
abbrev limitEvaluation : LimitStage diagram cone ⥤ Target :=
  inducedFunctor (limitEvaluationObj diagram cone)

/-- The functor from `Stage diagram stage` to `LimitStage diagram cone` forgetting the arrow of a
presentation, acting on morphisms by the leg of `cone` conjugated by `cone.comparison`. -/
def limitLeg (stage : Index) : Stage diagram stage ⥤ LimitStage diagram cone where
  obj object := ULift.up ⟨object.origin, object.object⟩
  map {source target} morphism := InducedCategory.homMk
    ((cone.comparison source.arrow).inv.app source.object ≫
      (cone.leg stage).map morphism.hom ≫
      (cone.comparison target.arrow).hom.app target.object)
  map_id object := by
    apply InducedCategory.hom_ext
    simp only [InducedCategory.id_hom, CategoryTheory.Functor.map_id,
      InducedCategory.homMk_hom]
    exact (congrArg ((cone.comparison object.arrow).inv.app object.object ≫ ·)
      (Category.id_comp ((cone.comparison object.arrow).hom.app object.object))).trans
      ((cone.comparison object.arrow).inv_hom_id_app object.object)
  map_comp first second := by
    apply InducedCategory.hom_ext
    simp

/-- The inverse of `cone.comparison` along a composite, followed by the leg of the composition
isomorphism of `diagram`, is the composite of the inverses along each arrow. -/
@[reassoc]
lemma cone_composition_inv {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : diagram.obj ⟨source⟩) :
    (cone.comparison (first ≫ second)).inv.app object ≫
        (cone.leg target).map
          ((diagram.mapComp first.toLoc second.toLoc).hom.toNatTrans.app object) =
      (cone.comparison first).inv.app object ≫
        (cone.comparison second).inv.app ((diagram.map first.toLoc).toFunctor.obj object) := by
  apply (cancel_mono
    ((cone.comparison second).hom.app ((diagram.map first.toLoc).toFunctor.obj object) ≫
      (cone.comparison first).hom.app object)).mp
  simp only [Category.assoc]
  rw [cone.comp]
  simp

/-- The leg of the inverse composition isomorphism of `diagram`, followed by `cone.comparison`
along the composite, is the composite of `cone.comparison` along each arrow. -/
@[reassoc]
lemma cone_composition_hom {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : diagram.obj ⟨source⟩) :
    (cone.leg target).map
        ((diagram.mapComp first.toLoc second.toLoc).inv.toNatTrans.app object) ≫
        (cone.comparison (first ≫ second)).hom.app object =
      (cone.comparison second).hom.app ((diagram.map first.toLoc).toFunctor.obj object) ≫
        (cone.comparison first).hom.app object := by
  rw [← cone.comp]
  simp [← Functor.map_comp_assoc]

/-- `push diagram arrow` followed by `limitLeg` at the target is `limitLeg` at the source. -/
lemma limitLeg_naturality {source target : Index} (arrow : source ⟶ target) :
    push diagram arrow ⋙ limitLeg diagram cone target = limitLeg diagram cone source := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro sourceObject targetObject morphism
  apply InducedCategory.hom_ext
  dsimp [limitLeg, push, comparison, Cat.Hom.toNatIso]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [cone_composition_inv_assoc, cone_composition_hom]
  erw [(cone.comparison arrow).hom.naturality_assoc morphism.hom]
  simp

/-- The cocone over `strictDiagram diagram` with apex `LimitStage diagram cone` and legs
`limitLeg diagram cone`. -/
def strictCocone : Cocone (strictDiagram diagram) where
  pt := Cat.of (LimitStage diagram cone)
  ι.app stage := (limitLeg diagram cone stage).toCatHom
  ι.naturality source target arrow := by
    apply Cat.Hom.ext
    exact limitLeg_naturality diagram cone arrow

/-- If every object of `Target` is isomorphic to the image of an object at some stage under the
leg of `cone`, then `limitEvaluation` is an equivalence `LimitStage diagram cone ≌ Target`. -/
def limitEquivalence
    (descent : ∀ object : Target, ∃ (stage : Index) (model : diagram.obj ⟨stage⟩),
      Nonempty ((cone.leg stage).obj model ≅ object)) : LimitStage diagram cone ≌ Target := by
  letI : (limitEvaluation diagram cone).EssSurj :=
    { mem_essImage := fun object ↦ by
        obtain ⟨stage, model, isomorphism⟩ := descent object
        exact ⟨ULift.up ⟨stage, model⟩, isomorphism⟩ }
  letI : (limitEvaluation diagram cone).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  exact (limitEvaluation diagram cone).asEquivalence

/-- `canonicalInverse` followed by the leg of `strictCocone diagram cone` and `limitEvaluation`
is isomorphic to the leg of `cone` at `stage`. -/
def canonicalLegIso (stage : Index) :
    canonicalInverse diagram stage ⋙ ((strictCocone diagram cone).ι.app stage).toFunctor ⋙
      limitEvaluation diagram cone ≅ cone.leg stage :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro source target morphism
    simpa [canonicalInverse, strictCocone, limitLeg, limitEvaluation] using
      NatIso.naturality_1 (cone.comparison (𝟙 stage)) morphism)

/-- Over a filtered index category, two presentations at `stage` with the same image under
`limitLeg` become equal after pushing along some arrow out of `stage`. -/
lemma limitLeg_objects_eventually_equal [IsFiltered Index]
    (stage : Index) (first second : Stage diagram stage)
    (equality : (limitLeg diagram cone stage).obj first =
      (limitLeg diagram cone stage).obj second) :
    ∃ (later : Index) (arrow : stage ⟶ later),
      (push diagram arrow).obj first = (push diagram arrow).obj second := by
  rcases first with ⟨origin, firstArrow, object⟩
  rcases second with ⟨otherOrigin, secondArrow, otherObject⟩
  have origin_eq : origin = otherOrigin :=
    congrArg (fun object : LimitStage diagram cone ↦ object.down.1) equality
  subst otherOrigin
  have object_eq : object = otherObject := by
    have pair_eq : (⟨origin, object⟩ : Σ stage : Index, diagram.obj ⟨stage⟩) =
        ⟨origin, otherObject⟩ := congrArg ULift.down equality
    exact eq_of_heq (Sigma.mk.inj_iff.mp pair_eq).2
  subst otherObject
  refine ⟨IsFiltered.coeq firstArrow secondArrow, IsFiltered.coeqHom firstArrow secondArrow, ?_⟩
  change Presentation.mk origin
      (firstArrow ≫ IsFiltered.coeqHom firstArrow secondArrow) object =
    Presentation.mk origin (secondArrow ≫ IsFiltered.coeqHom firstArrow secondArrow) object
  rw [IsFiltered.coeq_condition]

/-- Over a filtered index category, the objects of the apex of `strictCocone diagram cone` are the
colimit of the objects of the stages of `strictDiagram diagram`. -/
def strictCocone_objects_isColimit [IsFiltered Index] :
    IsColimit (Cat.objects.mapCocone (strictCocone diagram cone)) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun object ↦ ⟨object.down.1, ⟨object.down.1, 𝟙 object.down.1, object.down.2⟩, rfl⟩)
    (fun stage first second equality ↦
      limitLeg_objects_eventually_equal diagram cone stage first second equality)

/-- Conjugating the transport along an equality `first = alternate` by `cone.comparison` gives
the identity. -/
lemma cone_comparison_transport {source target : Index}
    {first alternate : source ⟶ target} (equality : first = alternate)
    (object : diagram.obj ⟨source⟩) :
    (cone.comparison first).inv.app object ≫
        eqToHom (congrArg (fun arrow : source ⟶ target ↦
          (cone.leg target).obj ((diagram.map arrow.toLoc).toFunctor.obj object)) equality) ≫
        (cone.comparison alternate).hom.app object = 𝟙 _ := by
  subst alternate
  simp

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- If `cone.comparison` along identities is the leg of the unit isomorphism of `diagram`, then
the isomorphisms `canonicalLegIso` are compatible with the cocone condition of
`strictCocone diagram cone`, with `canonicalTransitionIso` and with `cone.comparison`. -/
lemma canonicalLeg_compatibility
    (unit : ∀ (stage : Index) (object : diagram.obj ⟨stage⟩),
      (cone.comparison (𝟙 stage)).hom.app object =
        (cone.leg stage).map ((diagram.mapId ⟨stage⟩).hom.toNatTrans.app object))
    {source target : Index} (arrow : source ⟶ target) (object : diagram.obj ⟨source⟩) :
    let mapCoconeIso : ((strictDiagram diagram).map arrow).toFunctor ⋙
        ((strictCocone diagram cone).ι.app target).toFunctor ≅
          ((strictCocone diagram cone).ι.app source).toFunctor :=
      eqToIso (congrArg Cat.Hom.toFunctor ((strictCocone diagram cone).w arrow))
    let representative := (canonicalStageEquivalence diagram source).inverse.obj object
    let intermediate := (canonicalStageEquivalence diagram target).functor.obj
      (((strictDiagram diagram).map arrow).toFunctor.obj representative)
    (limitEvaluation diagram cone).map (mapCoconeIso.hom.app representative) ≫
        (canonicalLegIso diagram cone source).hom.app object =
      (((strictCocone diagram cone).ι.app target).toFunctor ⋙ limitEvaluation diagram cone).map
          ((canonicalStageEquivalence diagram target).unitIso.hom.app
            (((strictDiagram diagram).map arrow).toFunctor.obj representative)) ≫
        (canonicalLegIso diagram cone target).hom.app intermediate ≫
        (cone.leg target).map ((canonicalTransitionIso diagram arrow).hom.app object) ≫
        (cone.comparison arrow).hom.app object := by
  dsimp only
  simp [canonicalLegIso, canonicalStageEquivalence, canonicalUnitIso, canonicalInverse,
    strictCocone, limitLeg, canonicalTransitionIso_hom_app, unit, eqToHom_map,
    ← Functor.map_comp]
  simp [strictDiagram, push, pushObject]
  exact (cone_comparison_transport diagram cone (Category.id_comp arrow) object).symm

end Strictification

namespace Strictification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Nerve

universe uIndex vIndex uObj

/-- A cocone over a filtered diagram of categories is a colimit if, in each degree of the
2-truncated nerve, every simplex of the apex comes from some stage and two simplices at a stage
with equal images become equal at a later stage. -/
def catIsColimitOfTruncatedNerve
    {Index : Type uIndex} [Category.{vIndex} Index] [IsFiltered Index]
    (diagram : Index ⥤ Cat.{uObj, uObj}) (cone : Cocone diagram)
    (surjective : ∀ simplex : (SimplexCategory.Truncated 2)ᵒᵖ,
      ∀ object : (nerveFunctor₂.obj cone.pt).obj simplex,
      ∃ (stage : Index) (model : (nerveFunctor₂.obj (diagram.obj stage)).obj simplex),
        object = (nerveFunctor₂.map (cone.ι.app stage)).app simplex model)
    (eventually_equal : ∀ (simplex : (SimplexCategory.Truncated 2)ᵒᵖ) (stage : Index)
      (first second : (nerveFunctor₂.obj (diagram.obj stage)).obj simplex),
      (nerveFunctor₂.map (cone.ι.app stage)).app simplex first =
        (nerveFunctor₂.map (cone.ι.app stage)).app simplex second →
      ∃ (later : Index) (arrow : stage ⟶ later),
        (nerveFunctor₂.map (diagram.map arrow)).app simplex first =
          (nerveFunctor₂.map (diagram.map arrow)).app simplex second) :
    IsColimit cone := by
  apply isColimitOfReflects nerveFunctor₂
  refine evaluationJointlyReflectsColimits _ ?_
  intro simplex
  exact Types.FilteredColimit.isColimitOf' _ _ (surjective simplex) (eventually_equal simplex)

end Strictification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Nerve Opposite

namespace Strictification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

universe uIndex vIndex uCat

variable {Index : Type uIndex} [Category.{vIndex} Index] [IsFiltered Index]

/-- The functor sending a category to the set of `degree`-simplices of its nerve. -/
abbrev nerveLevel (degree : ℕ) : Cat.{uCat, uCat} ⥤ Type uCat :=
  nerveFunctor ⋙ (CategoryTheory.evaluation _ _).obj (op (SimplexCategory.mk degree))

/-- A functor sends the 1-simplex `ComposableArrows.mk₁ arrow` to the 1-simplex of the image of
`arrow`. -/
lemma nerveLevel_map_mk₁ {source target : Cat.{uCat, uCat}}
    (functor : source ⟶ target) {first second : source} (arrow : first ⟶ second) :
    (nerveLevel 1).map functor (ComposableArrows.mk₁ arrow) =
      ComposableArrows.mk₁ (functor.toFunctor.map arrow) :=
  nerveMap_app_mk₁ functor.toFunctor arrow

/-- The arrows of the image of a simplex under a functor are the images of its arrows. -/
@[simp]
lemma nerveLevel_map_map' {source target : Cat.{uCat, uCat}} (functor : source ⟶ target)
    {degree : ℕ} (simplex : ComposableArrows source degree)
    (first second : ℕ) (ordered : first ≤ second) (bound : second ≤ degree) :
    ((nerveLevel degree).map functor simplex).map' first second ordered bound =
      functor.toFunctor.map (simplex.map' first second ordered bound) := rfl

/-- `ComposableArrows.arrowEquiv` sends `ComposableArrows.mk₁ arrow` to `Arrow.mk arrow`. -/
@[simp]
lemma arrowEquiv_mk₁ {category : Type uCat} [Category.{uCat} category]
    {source target : category} (arrow : source ⟶ target) :
    ComposableArrows.arrowEquiv (ComposableArrows.mk₁ arrow) = Arrow.mk arrow := rfl

variable (diagram : Index ⥤ Cat.{uCat, uCat}) (cone : Cocone diagram)

/-- The action on simplices of the transition functor along a composite is the composite of the
actions. -/
lemma nerveLevel_map_comp (degree : ℕ) {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (simplex : (nerveLevel degree).obj (diagram.obj source)) :
    (nerveLevel degree).map (diagram.map (first ≫ second)) simplex =
      (nerveLevel degree).map (diagram.map second)
        ((nerveLevel degree).map (diagram.map first) simplex) := by
  rw [diagram.map_comp, Functor.map_comp]
  rfl

/-- The action on simplices of a transition functor followed by the leg of `cone` at its target is
that of the leg at its source. -/
lemma nerveLevel_leg_map (degree : ℕ) {source target : Index}
    (arrow : source ⟶ target)
    (simplex : (nerveLevel degree).obj (diagram.obj source)) :
    (nerveLevel degree).map (cone.ι.app target)
        ((nerveLevel degree).map (diagram.map arrow) simplex) =
      (nerveLevel degree).map (cone.ι.app source) simplex := by
  change ((nerveLevel degree).map (diagram.map arrow) ≫
    (nerveLevel degree).map (cone.ι.app target)) simplex = _
  rw [← Functor.map_comp, cone.w arrow]
  rfl

/-- If the objects of the apex of `cone` are the colimit of the objects of the stages, every
0-simplex of the apex comes from some stage. -/
lemma nerveLevel_zero_surjective
    (objects : IsColimit (Cat.objects.mapCocone cone))
    (simplex : (nerveLevel 0).obj cone.pt) :
    ∃ (stage : Index) (model : (nerveLevel 0).obj (diagram.obj stage)),
      simplex = (nerveLevel 0).map (cone.ι.app stage) model := by
  obtain ⟨stage, model, equality⟩ := Types.jointly_surjective_of_isColimit objects simplex.left
  refine ⟨stage, ComposableArrows.mk₀ model, ?_⟩
  exact ComposableArrows.ext₀ equality.symm

/-- If the objects of the apex of `cone` are the colimit of the objects of the stages, two
0-simplices at a stage with equal images become equal at a later stage. -/
lemma nerveLevel_zero_eventually_equal
    (objects : IsColimit (Cat.objects.mapCocone cone))
    (stage : Index) (first second : (nerveLevel 0).obj (diagram.obj stage))
    (equality : (nerveLevel 0).map (cone.ι.app stage) first =
      (nerveLevel 0).map (cone.ι.app stage) second) :
    ∃ (later : Index) (arrow : stage ⟶ later),
      (nerveLevel 0).map (diagram.map arrow) first =
        (nerveLevel 0).map (diagram.map arrow) second := by
  obtain ⟨later, arrow, equality⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' objects first.left second.left).mp
      (congrArg (fun simplex : ComposableArrows cone.pt 0 ↦ simplex.left) equality)
  exact ⟨later, arrow, ComposableArrows.ext₀ equality⟩

/-- If the 1-simplices of the apex of `cone` are the colimit of those of the stages, two
2-simplices at a stage with equal images become equal at a later stage. -/
lemma nerveLevel_two_eventually_equal
    (arrows : IsColimit ((nerveLevel 1).mapCocone cone))
    (stage : Index) (first second : (nerveLevel 2).obj (diagram.obj stage))
    (equality : (nerveLevel 2).map (cone.ι.app stage) first =
      (nerveLevel 2).map (cone.ι.app stage) second) :
    ∃ (later : Index) (arrow : stage ⟶ later),
      (nerveLevel 2).map (diagram.map arrow) first =
        (nerveLevel 2).map (diagram.map arrow) second := by
  change ComposableArrows (diagram.obj stage) 2 at first second
  have simplexEquality : ∀ (i j : ℕ) (ordered : i ≤ j) (bound : j ≤ 2),
      (nerveLevel 1).map (cone.ι.app stage) (ComposableArrows.mk₁ (first.map' i j ordered bound)) =
        (nerveLevel 1).map (cone.ι.app stage)
          (ComposableArrows.mk₁ (second.map' i j ordered bound)) := fun i j ordered bound ↦ by
    simpa only [nerveLevel_map_mk₁, nerveLevel_map_map'] using
      congrArg (fun simplex : ComposableArrows cone.pt 2 ↦
        ComposableArrows.mk₁ (simplex.map' i j ordered bound)) equality
  have leftEquality := simplexEquality 0 1 (by decide) (by decide)
  have rightEquality := simplexEquality 1 2 (by decide) (by decide)
  obtain ⟨middle, firstArrow, firstEq⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' arrows _ _).mp leftEquality
  obtain ⟨later, secondArrow, secondEq⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' arrows
      ((nerveLevel 1).map (diagram.map firstArrow)
        (ComposableArrows.mk₁ (first.map' 1 2)))
      ((nerveLevel 1).map (diagram.map firstArrow)
        (ComposableArrows.mk₁ (second.map' 1 2)))).mp
      (by
        change (nerveLevel 1).map (cone.ι.app middle) _ = (nerveLevel 1).map (cone.ι.app middle) _
        rw [nerveLevel_leg_map, nerveLevel_leg_map]
        exact rightEquality)
  change (nerveLevel 1).map (diagram.map firstArrow) _ =
    (nerveLevel 1).map (diagram.map firstArrow) _ at firstEq
  have firstEq' := congrArg ((nerveLevel 1).map (diagram.map secondArrow)) firstEq
  change (nerveLevel 1).map (diagram.map secondArrow) _ =
    (nerveLevel 1).map (diagram.map secondArrow) _ at secondEq
  refine ⟨later, firstArrow ≫ secondArrow, ?_⟩
  apply ComposableArrows.ext₂_of_arrow
  · rw [← nerveLevel_map_comp, ← nerveLevel_map_comp] at firstEq'
    simpa only [nerveLevel_map_mk₁, nerveLevel_map_map', arrowEquiv_mk₁] using
      congrArg ComposableArrows.arrowEquiv firstEq'
  · rw [← nerveLevel_map_comp, ← nerveLevel_map_comp] at secondEq
    simpa only [nerveLevel_map_mk₁, nerveLevel_map_map', arrowEquiv_mk₁] using
      congrArg ComposableArrows.arrowEquiv secondEq

/-- If the objects and the 1-simplices of the apex of `cone` are the colimits of those of the
stages, every 2-simplex of the apex comes from some stage. -/
lemma nerveLevel_two_surjective
    (objects : IsColimit (Cat.objects.mapCocone cone))
    (arrows : IsColimit ((nerveLevel 1).mapCocone cone))
    (simplex : (nerveLevel 2).obj cone.pt) :
    ∃ (stage : Index) (model : (nerveLevel 2).obj (diagram.obj stage)),
      simplex = (nerveLevel 2).map (cone.ι.app stage) model := by
  obtain ⟨source, middle, target, first, second, rfl⟩ := ComposableArrows.mk₂_surjective simplex
  obtain ⟨stage, firstModel, secondModel, firstEq, secondEq⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ arrows
      (ComposableArrows.mk₁ first) (ComposableArrows.mk₁ second)
  have middleEq : (cone.ι.app stage).toFunctor.obj firstModel.right =
      (cone.ι.app stage).toFunctor.obj secondModel.left :=
    (congrArg (fun simplex : ComposableArrows cone.pt 1 ↦ simplex.right) firstEq).trans
      (congrArg (fun simplex : ComposableArrows cone.pt 1 ↦ simplex.left) secondEq).symm
  obtain ⟨later, arrow, middleEq⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' objects firstModel.right secondModel.left).mp middleEq
  change (diagram.map arrow).toFunctor.obj firstModel.right =
    (diagram.map arrow).toFunctor.obj secondModel.left at middleEq
  let firstLater := (diagram.map arrow).toFunctor.map firstModel.hom
  let secondLater := eqToHom middleEq ≫ (diagram.map arrow).toFunctor.map secondModel.hom
  refine ⟨later, ComposableArrows.mk₂ firstLater secondLater, ?_⟩
  apply ComposableArrows.ext₂_of_arrow
  · have equality := (nerveLevel_leg_map diagram cone 1 arrow firstModel).trans firstEq
    exact (congrArg ComposableArrows.arrowEquiv equality).symm
  · have equality := (nerveLevel_leg_map diagram cone 1 arrow secondModel).trans secondEq
    have transport := ComposableArrows.mk₁_eqToHom_comp
      (congrArg (cone.ι.app later).toFunctor.obj middleEq)
      ((cone.ι.app later).toFunctor.map ((diagram.map arrow).toFunctor.map secondModel.hom))
    have equality' := congrArg ComposableArrows.arrowEquiv transport
    change Arrow.mk second = Arrow.mk ((cone.ι.app later).toFunctor.map secondLater)
    simpa only [secondLater, Functor.map_comp, eqToHom_map, arrowEquiv_mk₁] using
      (congrArg ComposableArrows.arrowEquiv equality).symm.trans equality'.symm

/-- A cocone over a filtered diagram of categories is a colimit if the objects and the
1-simplices of its apex are the colimits of those of the stages. -/
def catIsColimit_of_objects_and_arrows
    (objects : IsColimit (Cat.objects.mapCocone cone))
    (arrows : IsColimit ((nerveLevel 1).mapCocone cone)) : IsColimit cone := by
  apply isColimitOfReflects nerveFunctor₂
  refine evaluationJointlyReflectsColimits _ ?_
  intro simplex
  obtain ⟨⟨⟨degree⟩, bound⟩⟩ := simplex
  have bound' : degree ≤ 2 := bound
  interval_cases degree
  · exact Types.FilteredColimit.isColimitOf' _ _
      (nerveLevel_zero_surjective diagram cone objects)
      (nerveLevel_zero_eventually_equal diagram cone objects)
  · exact arrows
  · exact Types.FilteredColimit.isColimitOf' _ _
      (nerveLevel_two_surjective diagram cone objects arrows)
      (nerveLevel_two_eventually_equal diagram cone arrows)

end Strictification

namespace Strictification

open CategoryTheory CategoryTheory.Bicategory

universe w v u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The pseudofunctor `Cat.{v, u} ⥤ᵖ Cat.{max w v u, max w v u}` sending a category to its
`AsSmall` copy and a functor to its conjugate by `AsSmall.down` and `AsSmall.up`. -/
def smallCatPseudofunctor : Cat.{v, u} ⥤ᵖ Cat.{max w v u, max w v u} where
  obj category := Cat.of (AsSmall.{w} category)
  map functor := (AsSmall.down ⋙ functor.toFunctor ⋙ AsSmall.up).toCatHom
  map₂ transformation :=
    (Functor.whiskerLeft AsSmall.down
      (Functor.whiskerRight transformation.toNatTrans AsSmall.up)).toCatHom₂
  mapId category := eqToIso (by apply Cat.Hom.ext; rfl)
  mapComp first second := eqToIso (by apply Cat.Hom.ext; rfl)
  map₂_id functor := by
    apply Cat.Hom₂.ext
    ext object
    rfl
  map₂_comp first second := by
    apply Cat.Hom₂.ext
    ext object
    rfl
  map₂_whisker_left := by
    intro source middle target functor first second transformation
    apply Cat.Hom₂.ext
    ext object
    apply ULift.ext
    simp
  map₂_whisker_right transformation functor := by
    apply Cat.Hom₂.ext
    ext object
    apply ULift.ext
    simp
  map₂_associator first second third := by
    apply Cat.Hom₂.ext
    ext object
    apply ULift.ext
    simp
  map₂_left_unitor functor := by
    apply Cat.Hom₂.ext
    ext object
    apply ULift.ext
    simp
  map₂_right_unitor functor := by
    apply Cat.Hom₂.ext
    ext object
    apply ULift.ext
    simp

end Strictification

namespace Strictification

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

universe uIndex vIndex uObject

variable {Index : Type uIndex} [Category.{vIndex} Index] [IsFiltered Index]
variable (diagram : LocallyDiscrete Index ⥤ᵖ
  Cat.{max uIndex vIndex uObject, max uIndex vIndex uObject})
variable {Target : Type (max uIndex vIndex uObject)}
  [Category.{max uIndex vIndex uObject} Target] (cone : ConeData diagram Target)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Morphisms between images under `limitLeg diagram cone` descend to finite stages. -/
structure MorphismDescent where
  /-- Every morphism between images under `limitLeg` is the image of a morphism after pushing
  along some arrow. -/
  surjective : ∀ (stage : Index) (source target : Stage diagram stage)
    (morphism : (limitLeg diagram cone stage).obj source ⟶
      (limitLeg diagram cone stage).obj target),
    ∃ (later : Index) (arrow : stage ⟶ later)
      (model : (push diagram arrow).obj source ⟶ (push diagram arrow).obj target),
      (limitLeg diagram cone later).map model = morphism
  /-- Two morphisms with equal images under `limitLeg` become equal after pushing along some
  arrow. -/
  eventually_injective : ∀ (stage : Index) (source target : Stage diagram stage)
    (first second : source ⟶ target),
    (limitLeg diagram cone stage).map first = (limitLeg diagram cone stage).map second →
    ∃ (later : Index) (arrow : stage ⟶ later),
      (push diagram arrow).map first = (push diagram arrow).map second

/-- Morphisms in `Target` between images under the legs of `cone` descend to finite stages. -/
structure HomDescent where
  /-- Every morphism between images under the leg at a stage is, up to `cone.comparison`, the
  image of a morphism under the leg at a later stage. -/
  surjective : ∀ (stage : Index) (source target : diagram.obj ⟨stage⟩)
    (morphism : (cone.leg stage).obj source ⟶ (cone.leg stage).obj target),
    ∃ (later : Index) (arrow : stage ⟶ later)
      (model : (diagram.map arrow.toLoc).toFunctor.obj source ⟶
        (diagram.map arrow.toLoc).toFunctor.obj target),
      (cone.comparison arrow).inv.app source ≫ (cone.leg later).map model ≫
        (cone.comparison arrow).hom.app target = morphism
  /-- Two morphisms at a stage with equal images under the leg become equal under the
  transition functor along some arrow. -/
  eventually_injective : ∀ (stage : Index) (source target : diagram.obj ⟨stage⟩)
    (first second : source ⟶ target),
    (cone.leg stage).map first = (cone.leg stage).map second →
    ∃ (later : Index) (arrow : stage ⟶ later),
      (diagram.map arrow.toLoc).toFunctor.map first =
        (diagram.map arrow.toLoc).toFunctor.map second

omit [IsFiltered Index] in
/-- Descent of morphisms through the legs of `cone` implies descent of morphisms through
`limitLeg diagram cone`. -/
theorem HomDescent.toMorphismDescent
    (descent : HomDescent.{uIndex, vIndex, uObject} diagram cone) :
    MorphismDescent.{uIndex, vIndex, uObject} diagram cone where
  surjective stage source target morphism := by
    obtain ⟨later, arrow, model, equality⟩ := descent.surjective stage
      ((evaluation diagram stage).obj source) ((evaluation diagram stage).obj target)
      ((cone.comparison source.arrow).hom.app source.object ≫ morphism.hom ≫
        (cone.comparison target.arrow).inv.app target.object)
    let lifted : (push diagram arrow).obj source ⟶ (push diagram arrow).obj target :=
      InducedCategory.homMk ((comparison diagram arrow source).hom ≫ model ≫
        (comparison diagram arrow target).inv)
    refine ⟨later, arrow, lifted, ?_⟩
    apply InducedCategory.hom_ext
    dsimp [lifted, limitLeg, comparison, Cat.Hom.toNatIso, push, pushObject]
    simp only [Functor.map_comp, Category.assoc]
    rw [cone_composition_inv_assoc, cone_composition_hom]
    have transported := congrArg (fun value ↦
      (cone.comparison source.arrow).inv.app source.object ≫ value ≫
        (cone.comparison target.arrow).hom.app target.object) equality
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app] at transported
    exact transported.trans (Category.comp_id morphism.hom)
  eventually_injective stage source target first second equality := by
    have underlying : (cone.leg stage).map first.hom = (cone.leg stage).map second.hom := by
      apply (cancel_epi ((cone.comparison source.arrow).inv.app source.object)).mp
      apply (cancel_mono ((cone.comparison target.arrow).hom.app target.object)).mp
      simpa only [limitLeg, InducedCategory.homMk_hom, Category.assoc] using
        congrArg (fun morphism ↦ morphism.hom) equality
    obtain ⟨later, arrow, equality⟩ := descent.eventually_injective stage
      ((evaluation diagram stage).obj source) ((evaluation diagram stage).obj target)
      first.hom second.hom underlying
    refine ⟨later, arrow, ?_⟩
    apply InducedCategory.hom_ext
    simp only [push, InducedCategory.homMk_hom, equality]

variable (descent : MorphismDescent.{uIndex, vIndex, uObject} diagram cone)

include descent

/-- Under `MorphismDescent`, every 1-simplex of the apex of `strictCocone diagram cone` comes
from some stage. -/
lemma strictCocone_arrows_surjective
    (simplex : (nerveLevel 1).obj (strictCocone diagram cone).pt) :
    ∃ (stage : Index) (model : (nerveLevel 1).obj ((strictDiagram diagram).obj stage)),
      simplex = (nerveLevel 1).map ((strictCocone diagram cone).ι.app stage) model := by
  obtain ⟨source, target, morphism, rfl⟩ := ComposableArrows.mk₁_surjective simplex
  rcases source with ⟨⟨sourceStage, sourceObject⟩⟩
  rcases target with ⟨⟨targetStage, targetObject⟩⟩
  let stage := IsFiltered.max sourceStage targetStage
  let source : Stage diagram stage :=
    ⟨sourceStage, IsFiltered.leftToMax sourceStage targetStage, sourceObject⟩
  let target : Stage diagram stage :=
    ⟨targetStage, IsFiltered.rightToMax sourceStage targetStage, targetObject⟩
  obtain ⟨later, arrow, model, equality⟩ := descent.surjective stage source target morphism
  refine ⟨later, ComposableArrows.mk₁ model, ?_⟩
  rw [nerveLevel_map_mk₁]
  change ComposableArrows.mk₁ morphism =
    ComposableArrows.mk₁ ((limitLeg diagram cone later).map model)
  rw [equality]

omit [IsFiltered Index] in
/-- Under `MorphismDescent`, two 1-simplices at a stage with the same endpoints and equal images
under the leg of `strictCocone diagram cone` become equal at a later stage. -/
lemma strictCocone_arrows_eventually_equal_of_objects_equal
    (stage : Index) (first second : (nerveLevel 1).obj ((strictDiagram diagram).obj stage))
    (sourceEquality : first.left = second.left) (targetEquality : first.right = second.right)
    (equality : (nerveLevel 1).map ((strictCocone diagram cone).ι.app stage) first =
      (nerveLevel 1).map ((strictCocone diagram cone).ι.app stage) second) :
    ∃ (later : Index) (arrow : stage ⟶ later),
      (nerveLevel 1).map ((strictDiagram diagram).map arrow) first =
        (nerveLevel 1).map ((strictDiagram diagram).map arrow) second := by
  obtain ⟨source, target, firstMorphism, rfl⟩ := ComposableArrows.mk₁_surjective first
  obtain ⟨otherSource, otherTarget, secondMorphism, rfl⟩ := ComposableArrows.mk₁_surjective second
  change source = otherSource at sourceEquality
  change target = otherTarget at targetEquality
  subst otherSource otherTarget
  have homEquality := congrArg ComposableArrows.arrowEquiv equality
  simp only [nerveLevel_map_mk₁, arrowEquiv_mk₁, Arrow.mk_inj] at homEquality
  obtain ⟨later, arrow, equality⟩ :=
    descent.eventually_injective stage source target firstMorphism secondMorphism homEquality
  refine ⟨later, arrow, ?_⟩
  rw [nerveLevel_map_mk₁, nerveLevel_map_mk₁]
  change ComposableArrows.mk₁ ((push diagram arrow).map firstMorphism) =
    ComposableArrows.mk₁ ((push diagram arrow).map secondMorphism)
  exact congrArg ComposableArrows.mk₁ equality

/-- Under `MorphismDescent` over a filtered index category, two 1-simplices at a stage with equal
images under the leg of `strictCocone diagram cone` become equal at a later stage. -/
lemma strictCocone_arrows_eventually_equal
    (stage : Index) (first second : (nerveLevel 1).obj ((strictDiagram diagram).obj stage))
    (equality : (nerveLevel 1).map ((strictCocone diagram cone).ι.app stage) first =
      (nerveLevel 1).map ((strictCocone diagram cone).ι.app stage) second) :
    ∃ (later : Index) (arrow : stage ⟶ later),
      (nerveLevel 1).map ((strictDiagram diagram).map arrow) first =
        (nerveLevel 1).map ((strictDiagram diagram).map arrow) second := by
  have sourceEquality := congrArg
    (fun simplex : ComposableArrows (LimitStage diagram cone) 1 ↦ simplex.left) equality
  have targetEquality := congrArg
    (fun simplex : ComposableArrows (LimitStage diagram cone) 1 ↦ simplex.right) equality
  obtain ⟨middle, firstArrow, firstEq⟩ :=
    limitLeg_objects_eventually_equal diagram cone stage first.left second.left sourceEquality
  obtain ⟨later, secondArrow, secondEq⟩ :=
    limitLeg_objects_eventually_equal diagram cone middle
      ((push diagram firstArrow).obj first.right) ((push diagram firstArrow).obj second.right)
      targetEquality
  let firstLater := (nerveLevel 1).map ((strictDiagram diagram).map secondArrow)
    ((nerveLevel 1).map ((strictDiagram diagram).map firstArrow) first)
  let secondLater := (nerveLevel 1).map ((strictDiagram diagram).map secondArrow)
    ((nerveLevel 1).map ((strictDiagram diagram).map firstArrow) second)
  have sourceEq : firstLater.left = secondLater.left :=
    congrArg (push diagram secondArrow).obj firstEq
  have targetEq : firstLater.right = secondLater.right := secondEq
  have imageEq : (nerveLevel 1).map ((strictCocone diagram cone).ι.app later) firstLater =
      (nerveLevel 1).map ((strictCocone diagram cone).ι.app later) secondLater := by
    dsimp only [firstLater, secondLater]
    rw [nerveLevel_leg_map, nerveLevel_leg_map, nerveLevel_leg_map, nerveLevel_leg_map]
    exact equality
  obtain ⟨finalStage, finalArrow, equality⟩ :=
    strictCocone_arrows_eventually_equal_of_objects_equal.{uIndex, vIndex, uObject} diagram cone
      descent
      later firstLater secondLater sourceEq targetEq imageEq
  refine ⟨finalStage, firstArrow ≫ secondArrow ≫ finalArrow, ?_⟩
  simpa only [nerveLevel_map_comp, firstLater, secondLater] using equality

/-- Under `MorphismDescent` over a filtered index category, `strictCocone diagram cone` is a
colimit cocone. -/
def strictCocone_isColimit : IsColimit (strictCocone diagram cone) :=
  catIsColimit_of_objects_and_arrows (strictDiagram diagram) (strictCocone diagram cone)
    (strictCocone_objects_isColimit diagram cone)
    (Types.FilteredColimit.isColimitOf' _ _
      (strictCocone_arrows_surjective.{uIndex, vIndex, uObject} diagram cone descent)
      (strictCocone_arrows_eventually_equal.{uIndex, vIndex, uObject} diagram cone descent))

end Strictification

end PseudoCoherence

end

module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.StrictCocone
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.DerivedExtensionPseudofunctor
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RelativelyPerfectDiagram

/-!
# The filtered colimit of relatively perfect categories

Restriction to the terminal extension of the index category, the small terminal cocone, and
the filtered-colimit description of the category of relatively perfect objects (Stacks 0DHX).

This is part 10 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Nerve Opposite

namespace Strictification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

universe uIndex vIndex uObject vMorphism

variable {Index : Type uIndex} [Category.{vIndex} Index]
variable (diagram : LocallyDiscrete (WithTerminal Index) ⥤ᵖ Cat.{vMorphism, uObject})

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The restriction to `Index` of a pseudofunctor on `WithTerminal Index`. -/
abbrev terminalRestriction : LocallyDiscrete Index ⥤ᵖ Cat.{vMorphism, uObject} :=
  (WithTerminal.incl : Index ⥤ WithTerminal Index).toPseudofunctor.comp diagram

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The cocone over `terminalRestriction diagram` with apex the value of `diagram` at the terminal
object, whose legs are the transition functors to the terminal object. -/
def terminalConeData : ConeData (terminalRestriction diagram)
    (diagram.obj ⟨WithTerminal.star⟩) where
  leg stage := (diagram.map (WithTerminal.homFrom stage).toLoc).toFunctor
  comparison {source target} arrow :=
    (Cat.Hom.toNatIso (diagram.mapComp
      ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow).toLoc
      (WithTerminal.homFrom target).toLoc)).symm
  comp {source middle target} first second object := by
    dsimp [terminalRestriction, Cat.Hom.toNatIso, Quiver.Hom.toLoc]
    simp only [diagram.map₂_id, Cat.Hom₂.id_app, Category.id_comp]
    erw [diagram.mapComp_assoc_right_inv_app]
    simp [Strict.associator_eqToIso, ← Functor.map_comp_assoc,
      WithTerminal.incl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The comparison isomorphism of `terminalConeData diagram` along an identity is the leg of the
unit isomorphism of `terminalRestriction diagram`. -/
lemma terminalConeData_unit (stage : Index)
    (object : (terminalRestriction diagram).obj ⟨stage⟩) :
    ((terminalConeData diagram).comparison (𝟙 stage)).hom.app object =
      ((terminalConeData diagram).leg stage).map
        (((terminalRestriction diagram).mapId ⟨stage⟩).hom.toNatTrans.app object) := by
  dsimp [terminalConeData, terminalRestriction, Cat.Hom.toNatIso, Quiver.Hom.toLoc]
  simp [WithTerminal.incl]
  erw [diagram.mapComp_id_left_inv_app]
  simp [Strict.leftUnitor_eqToIso]
  erw [diagram.map₂_id, Cat.Hom₂.id_app, Category.id_comp]
  rfl

end Strictification

namespace Strictification

open CategoryTheory

universe w vSource uSource vTarget uTarget

variable {Source : Type uSource} [Category.{vSource} Source]
variable {Target : Type uTarget} [Category.{vTarget} Target]

set_option backward.isDefEq.respectTransparency false

/-- The unit of `equivalence.trans AsSmall.equiv.symm` is the unit of `equivalence`. -/
lemma transAsSmall_unit (equivalence : Source ≌ AsSmall.{w} Target) (object : Source) :
    (equivalence.trans AsSmall.equiv.symm).unitIso.hom.app object =
      equivalence.unitIso.hom.app object := by
  dsimp [CategoryTheory.Equivalence.trans, AsSmall.equiv, AsSmall.up, AsSmall.down]
  simp only [Category.id_comp, Category.comp_id]
  erw [equivalence.inverse.map_id]
  exact Category.comp_id _

/-- The counit of `equivalence.trans AsSmall.equiv.symm` is the image under `AsSmall.down` of the
counit of `equivalence`. -/
lemma transAsSmall_counit (equivalence : Source ≌ AsSmall.{w} Target) (object : Target) :
    (equivalence.trans AsSmall.equiv.symm).counitIso.hom.app object =
      AsSmall.down.map (equivalence.counitIso.hom.app (AsSmall.up.obj object)) := by
  dsimp [CategoryTheory.Equivalence.trans, AsSmall.equiv, AsSmall.up, AsSmall.down]
  simp only [Category.id_comp, Category.comp_id]

end Strictification

namespace Strictification

open CategoryTheory CategoryTheory.Bicategory

universe w uIndex vIndex uObject

variable {Index : Type uIndex} [Category.{vIndex} Index]
variable (diagram : LocallyDiscrete Index ⥤ᵖ Cat.{uObject, uObject})

set_option backward.isDefEq.respectTransparency false

/-- On underlying objects, the inverse unit isomorphism of `diagram.comp smallCatPseudofunctor`
is that of `diagram`. -/
lemma small_mapId_inv_app (stage : Index) (object : diagram.obj ⟨stage⟩) :
    ULift.down (((diagram.comp smallCatPseudofunctor.{w, uObject, uObject}).mapId
      ⟨stage⟩).inv.toNatTrans.app
      (ULift.up object)) = (diagram.mapId ⟨stage⟩).inv.toNatTrans.app object := by
  simp [Pseudofunctor.comp, smallCatPseudofunctor, AsSmall.up, AsSmall.down]

/-- On underlying objects, the inverse composition isomorphism of
`diagram.comp smallCatPseudofunctor` is that of `diagram`. -/
lemma small_mapComp_inv_app {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : diagram.obj ⟨source⟩) :
    ULift.down (((diagram.comp smallCatPseudofunctor.{w, uObject, uObject}).mapComp
      first.toLoc second.toLoc).inv.toNatTrans.app (ULift.up object)) =
      (diagram.mapComp first.toLoc second.toLoc).inv.toNatTrans.app object := by
  simp [Pseudofunctor.comp, smallCatPseudofunctor, AsSmall.up, AsSmall.down]

/-- On underlying objects, the composition isomorphism of `diagram.comp smallCatPseudofunctor` is
that of `diagram`. -/
lemma small_mapComp_hom_app {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : diagram.obj ⟨source⟩) :
    ULift.down (((diagram.comp smallCatPseudofunctor.{w, uObject, uObject}).mapComp
      first.toLoc second.toLoc).hom.toNatTrans.app (ULift.up object)) =
      (diagram.mapComp first.toLoc second.toLoc).hom.toNatTrans.app object := by
  simp [Pseudofunctor.comp, smallCatPseudofunctor, AsSmall.up, AsSmall.down]

end Strictification

namespace Strictification

open CategoryTheory CategoryTheory.Bicategory

universe uIndex vIndex uObject

variable {Index : Type uIndex} [Category.{vIndex} Index]
variable (original : LocallyDiscrete (WithTerminal Index) ⥤ᵖ Cat.{uObject, uObject})

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The restriction to `Index` of the composite of `original` with `smallCatPseudofunctor`. -/
abbrev smallTerminalDiagram :=
  terminalRestriction (original.comp smallCatPseudofunctor.{max uIndex vIndex, uObject, uObject})

/-- `ULift.down` of a composite in a stage of `smallTerminalDiagram original` is the composite of
the `ULift.down`s. -/
lemma smallTerminal_down_comp (stage : Index)
    {source middle target : (smallTerminalDiagram original).obj ⟨stage⟩}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    ULift.down (first ≫ second) = ULift.down first ≫ ULift.down second := rfl

/-- On underlying morphisms, the transition functors of `smallTerminalDiagram original` are those
of `original`. -/
lemma smallTerminal_down_map {source target : Index} (arrow : source ⟶ target)
    {first second : (smallTerminalDiagram original).obj ⟨source⟩} (morphism : first ⟶ second) :
    ULift.down (((smallTerminalDiagram original).map arrow.toLoc).toFunctor.map morphism) =
      (original.map ((WithTerminal.incl : Index ⥤ WithTerminal Index).map
        arrow).toLoc).toFunctor.map
        (ULift.down morphism) := rfl

/-- On underlying objects, the inverse unit isomorphism of `smallTerminalDiagram original` is that
of `original`. -/
lemma smallTerminal_mapId_inv_app (stage : Index)
    (object : original.obj ⟨WithTerminal.of stage⟩) :
    ULift.down (((smallTerminalDiagram original).mapId ⟨stage⟩).inv.toNatTrans.app (ULift.up
      object)) =
      (original.mapId ⟨WithTerminal.of stage⟩).inv.toNatTrans.app object := by
  dsimp [smallTerminalDiagram, terminalRestriction, Pseudofunctor.comp, smallCatPseudofunctor,
    Quiver.Hom.toLoc, AsSmall.up, AsSmall.down]
  simp only [Category.id_comp]
  erw [original.map₂_id, Cat.Hom₂.id_app]
  show _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- On underlying objects, the inverse composition isomorphism of `smallTerminalDiagram original`
is that of `original`. -/
lemma smallTerminal_mapComp_inv_app {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (object : original.obj ⟨WithTerminal.of source⟩) :
    ULift.down (((smallTerminalDiagram original).mapComp first.toLoc
      second.toLoc).inv.toNatTrans.app
      (ULift.up object)) =
      (original.mapComp ((WithTerminal.incl : Index ⥤ WithTerminal Index).map first).toLoc
        ((WithTerminal.incl : Index ⥤ WithTerminal Index).map second).toLoc).inv.toNatTrans.app
          object := by
  dsimp [smallTerminalDiagram, terminalRestriction, Pseudofunctor.comp, smallCatPseudofunctor,
    Quiver.Hom.toLoc, AsSmall.up, AsSmall.down]
  simp only [Category.id_comp]
  erw [original.map₂_id, Cat.Hom₂.id_app]
  show _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The equivalence between the stage of `strictDiagram (smallTerminalDiagram original)` at
`stage` and the value of `original` at `stage`. -/
def smallTerminalStageEquivalence (stage : Index) :
    (strictDiagram (smallTerminalDiagram original)).obj stage ≌
      original.obj ⟨WithTerminal.of stage⟩ :=
  (canonicalStageEquivalence (smallTerminalDiagram original) stage).trans
    AsSmall.equiv.{uObject, uObject, max uIndex vIndex}.symm

/-- Under the equivalences `smallTerminalStageEquivalence`, the transition functor of
`strictDiagram (smallTerminalDiagram original)` along `arrow` is isomorphic to that of
`original`. -/
def smallTerminalTransitionIso {source target : Index} (arrow : source ⟶ target) :
    (smallTerminalStageEquivalence original source).inverse ⋙
        ((strictDiagram (smallTerminalDiagram original)).map arrow).toFunctor ⋙
        (smallTerminalStageEquivalence original target).functor ≅
      (original.map ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow).toLoc).toFunctor :=
  Functor.isoWhiskerLeft (AsSmall.up.{uObject, uObject, max uIndex vIndex})
    (Functor.isoWhiskerRight (canonicalTransitionIso (smallTerminalDiagram original) arrow)
      AsSmall.down.{uObject, uObject, max uIndex vIndex})

attribute [local simp] transAsSmall_unit transAsSmall_counit

/-- The unit coherence of `smallTerminalTransitionIso`: at the identity of `stage` it is the
composite of the identity transport, the counit of `smallTerminalStageEquivalence` and the
inverse unit isomorphism of `original`. -/
lemma smallTerminalTransition_id (stage : Index)
    (object : original.obj ⟨WithTerminal.of stage⟩) :
    let G := strictDiagram (smallTerminalDiagram original)
    let eG := smallTerminalStageEquivalence original
    let identityIso : (G.map (𝟙 stage)).toFunctor ≅ 𝟭 (G.obj stage) :=
      eqToIso (congrArg Cat.Hom.toFunctor (G.map_id stage))
    (eG stage).functor.map (identityIso.hom.app ((eG stage).inverse.obj object)) ≫
      (eG stage).counitIso.hom.app object ≫
      (original.mapId ⟨WithTerminal.of stage⟩).inv.toNatTrans.app object =
        (smallTerminalTransitionIso original (𝟙 stage)).hom.app object := by
  dsimp only
  have counit : (smallTerminalStageEquivalence original stage).counitIso.hom.app object =
      AsSmall.down.{uObject, uObject, max uIndex vIndex}.map
        ((canonicalStageEquivalence (smallTerminalDiagram original) stage).counitIso.hom.app
          (ULift.up object)) :=
    transAsSmall_counit
      (show Stage (smallTerminalDiagram original) stage ≌
          AsSmall.{max uIndex vIndex} (original.obj ⟨WithTerminal.of stage⟩) from
        canonicalStageEquivalence (smallTerminalDiagram original) stage) object
  rw [counit]
  have coherence := canonicalTransition_id (smallTerminalDiagram original) stage (ULift.up object)
  have projected := congrArg ULift.down coherence
  simp only [smallTerminal_down_comp, smallTerminal_mapId_inv_app] at projected
  simpa [smallTerminalStageEquivalence, smallTerminalTransitionIso, AsSmall.up,
    AsSmall.down] using projected

/-- The unit of `smallTerminalStageEquivalence` is that of `canonicalStageEquivalence`. -/
private lemma smallTerminalStageEquivalence_unit_app (stage : Index)
    (object : Stage (smallTerminalDiagram original) stage) :
    (smallTerminalStageEquivalence original stage).unitIso.hom.app object =
      (canonicalStageEquivalence (smallTerminalDiagram original) stage).unitIso.hom.app object :=
  transAsSmall_unit
    (show Stage (smallTerminalDiagram original) stage ≌
        AsSmall.{max uIndex vIndex} (original.obj ⟨WithTerminal.of stage⟩) from
      canonicalStageEquivalence (smallTerminalDiagram original) stage) object

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The composition coherence of `smallTerminalTransitionIso`: along `first ≫ second` it is the
composite of the composition transport, the unit of `smallTerminalStageEquivalence`, the
isomorphisms along `second` and `first`, and the inverse composition isomorphism of
`original`. -/
lemma smallTerminalTransition_comp {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (object : original.obj ⟨WithTerminal.of source⟩) :
    let G := strictDiagram (smallTerminalDiagram original)
    let eG := smallTerminalStageEquivalence original
    let compositionIso : (G.map (first ≫ second)).toFunctor ≅
        (G.map first).toFunctor ⋙ (G.map second).toFunctor :=
      eqToIso (congrArg Cat.Hom.toFunctor (G.map_comp first second))
    let representative := (eG source).inverse.obj object
    let intermediate := (eG middle).functor.obj ((G.map first).toFunctor.obj representative)
    (eG target).functor.map (compositionIso.hom.app representative) ≫
      (eG target).functor.map ((G.map second).toFunctor.map
        ((eG middle).unitIso.hom.app ((G.map first).toFunctor.obj representative))) ≫
      (smallTerminalTransitionIso original second).hom.app intermediate ≫
      (original.map ((WithTerminal.incl : Index ⥤ WithTerminal Index).map
        second).toLoc).toFunctor.map
        ((smallTerminalTransitionIso original first).hom.app object) ≫
      (original.mapComp ((WithTerminal.incl : Index ⥤ WithTerminal Index).map first).toLoc
        ((WithTerminal.incl : Index ⥤ WithTerminal Index).map second).toLoc).inv.toNatTrans.app
          object =
      (smallTerminalTransitionIso original (first ≫ second)).hom.app object := by
  dsimp only
  rw [smallTerminalStageEquivalence_unit_app]
  have coherence :=
    canonicalTransition_comp (smallTerminalDiagram original) first second (ULift.up object)
  have projected := congrArg ULift.down coherence
  simp only [smallTerminal_down_comp, smallTerminal_mapComp_inv_app,
    smallTerminal_down_map] at projected
  simp [smallTerminalStageEquivalence, smallTerminalTransitionIso, AsSmall.up,
    AsSmall.down] at projected ⊢
  exact projected

/-- The cocone `terminalConeData` of the composite of `original` with `smallCatPseudofunctor`. -/
abbrev smallTerminalCone :=
  terminalConeData (original.comp smallCatPseudofunctor.{max uIndex vIndex, uObject, uObject})

/-- The cocone `strictCocone` over `strictDiagram (smallTerminalDiagram original)` determined by
`smallTerminalCone original`. -/
abbrev smallTerminalCocone :=
  strictCocone (smallTerminalDiagram original) (smallTerminalCone original)

/-- The functor from the apex of `smallTerminalCocone original` to the value of `original` at the
terminal object. -/
abbrev smallTerminalEvaluation :=
  limitEvaluation (smallTerminalDiagram original) (smallTerminalCone original) ⋙
    AsSmall.down.{uObject, uObject, max uIndex vIndex}

/-- Under `smallTerminalStageEquivalence`, the leg of `smallTerminalCocone original` at `stage`
followed by `smallTerminalEvaluation` is isomorphic to the transition functor of `original` to
the terminal object. -/
def smallTerminalLegIso (stage : Index) :
    (smallTerminalStageEquivalence original stage).inverse ⋙
        ((smallTerminalCocone original).ι.app stage).toFunctor ⋙ smallTerminalEvaluation original ≅
      (original.map (WithTerminal.homFrom stage).toLoc).toFunctor :=
  Functor.isoWhiskerLeft (AsSmall.up.{uObject, uObject, max uIndex vIndex})
    (Functor.isoWhiskerRight
      (canonicalLegIso (smallTerminalDiagram original) (smallTerminalCone original) stage)
      AsSmall.down.{uObject, uObject, max uIndex vIndex})

/-- `ULift.down` of a composite at the terminal object is the composite of the `ULift.down`s. -/
lemma smallTerminalLimit_down_comp
    {source middle target :
      (original.comp smallCatPseudofunctor.{max uIndex vIndex, uObject, uObject}).obj
        ⟨WithTerminal.star⟩}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    ULift.down (first ≫ second) = ULift.down first ≫ ULift.down second := rfl

/-- On underlying morphisms, the leg of `smallTerminalCone original` at `stage` is the transition
functor of `original` to the terminal object. -/
lemma smallTerminalLeg_down_map (stage : Index)
    {source target : (smallTerminalDiagram original).obj ⟨stage⟩} (morphism : source ⟶ target) :
    ULift.down (((smallTerminalCone original).leg stage).map morphism) =
      (original.map (WithTerminal.homFrom stage).toLoc).toFunctor.map (ULift.down morphism) := rfl

/-- On underlying objects, the comparison isomorphism of `smallTerminalCone original` is the
inverse composition isomorphism of `original`. -/
lemma smallTerminalComparison_hom {source target : Index} (arrow : source ⟶ target)
    (object : original.obj ⟨WithTerminal.of source⟩) :
    ULift.down (((smallTerminalCone original).comparison arrow).hom.app (ULift.up object)) =
      (original.mapComp ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow).toLoc
        (WithTerminal.homFrom target).toLoc).inv.toNatTrans.app object :=
  small_mapComp_inv_app.{max uIndex vIndex, uIndex, vIndex, uObject} original
    ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow) (WithTerminal.homFrom target)
      object

/-- On underlying objects, the inverse comparison isomorphism of `smallTerminalCone original` is
the composition isomorphism of `original`. -/
lemma smallTerminalComparison_inv {source target : Index} (arrow : source ⟶ target)
    (object : original.obj ⟨WithTerminal.of source⟩) :
    ULift.down (((smallTerminalCone original).comparison arrow).inv.app (ULift.up object)) =
      (original.mapComp ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow).toLoc
        (WithTerminal.homFrom target).toLoc).hom.toNatTrans.app object :=
  small_mapComp_hom_app.{max uIndex vIndex, uIndex, vIndex, uObject} original
    ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow) (WithTerminal.homFrom target)
      object

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The isomorphisms `smallTerminalLegIso` are compatible with the cocone condition of
`smallTerminalCocone original`, with `smallTerminalTransitionIso` and with the composition
isomorphisms of `original`. -/
lemma smallTerminalLeg_compatibility {source target : Index} (arrow : source ⟶ target)
    (object : original.obj ⟨WithTerminal.of source⟩) :
    let G := strictDiagram (smallTerminalDiagram original)
    let eG := smallTerminalStageEquivalence original
    let cocone := smallTerminalCocone original
    let mapCoconeIso : (G.map arrow).toFunctor ⋙ (cocone.ι.app target).toFunctor ≅
        (cocone.ι.app source).toFunctor :=
      eqToIso (congrArg Cat.Hom.toFunctor (cocone.w arrow))
    let representative := (eG source).inverse.obj object
    let intermediate := (eG target).functor.obj ((G.map arrow).toFunctor.obj representative)
    (smallTerminalEvaluation original).map (mapCoconeIso.hom.app representative) ≫
        (smallTerminalLegIso original source).hom.app object =
      ((cocone.ι.app target).toFunctor ⋙ smallTerminalEvaluation original).map
          ((eG target).unitIso.hom.app ((G.map arrow).toFunctor.obj representative)) ≫
        (smallTerminalLegIso original target).hom.app intermediate ≫
        (original.map (WithTerminal.homFrom target).toLoc).toFunctor.map
          ((smallTerminalTransitionIso original arrow).hom.app object) ≫
        (original.mapComp ((WithTerminal.incl : Index ⥤ WithTerminal Index).map arrow).toLoc
          (WithTerminal.homFrom target).toLoc).inv.toNatTrans.app object := by
  dsimp only
  rw [smallTerminalStageEquivalence_unit_app]
  have coherence :=
    canonicalLeg_compatibility (smallTerminalDiagram original) (smallTerminalCone original)
    (terminalConeData_unit (original.comp
      smallCatPseudofunctor.{max uIndex vIndex, uObject, uObject}))
    arrow (ULift.up object)
  have projected := congrArg ULift.down coherence
  simp only [smallTerminalLimit_down_comp, smallTerminalLeg_down_map,
    smallTerminalComparison_hom] at projected
  simp [smallTerminalStageEquivalence, smallTerminalTransitionIso, smallTerminalLegIso,
    smallTerminalEvaluation, AsSmall.up, AsSmall.down] at projected ⊢
  exact projected

end Strictification

set_option maxHeartbeats 1600000 in
-- elaborating the composite natural transformations of derived functors below
/-- Relatively perfect complexes descend through filtered colimits, derived Hom from a
pseudo-coherent complex to a complex of finite Tor-dimension commutes with such a colimit, and
the category of relatively perfect complexes over the limit is the categorical colimit of the
categories at the stages. -/
@[stacks 0DHX]
public theorem relativelyPerfectComplexes_filteredColimit
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D₀ : DerivedTensoringDatum.{uR, max uR uA uM} R₀)
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i))
    (Dlim : DerivedTensoringDatum.{uR, max uR uA uM} c.pt) :
    let E := fun {A B : Type (max uR uA)} [CommRing A] [CommRing B] (f : A →+* B) ↦
      totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f
    let liftBase : ULift.{uR} A₀ →+* A₀ := ULift.ringEquiv.toRingHom
    let W := (ModuleCat.restrictScalars.{max uR uA uM} liftBase).mapDerivedCategory
    let b := fun i : I ↦ (baseToStageMap F A₀ i).comp liftBase
    let blim := (baseToLimitMap c A₀).comp liftBase
    let B := fun i : I ↦ W ⋙ (E (b i)).functor
    let Blim := W ⋙ (E blim).functor
    let S := fun (i : I) ↦ E (stageToLimitMap c A₀ i)
    let P : ∀ i : I, ObjectProperty
        (DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i))) := fun i K ↦
      IsRelativelyPerfect.{uR, max uR uA, uM}
        (D i).tensor (D i).comparison (D i).isLeftDerived K
    let Plim : ObjectProperty
        (DerivedCategory (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀))) := fun K ↦
      IsRelativelyPerfect.{uR, max uR uA, uM}
        Dlim.tensor Dlim.comparison Dlim.isLeftDerived K
    ∃ (comp : ∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
          (f : A →+* B) (g : B →+* C),
          (E f).functor ⋙ (E g).functor ≅ (E (g.comp f)).functor)
      (unit : ∀ (A : Type (max uR uA)) [CommRing A],
        𝟭 (DerivedCategory (ModuleCat.{max uR uA uM} A)) ≅ (E (RingHom.id A)).functor),
      (∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
          (f : A →+* B) (g : B →+* C)
          (Q : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
        letI : (ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM} f).IsLeftAdjoint :=
          (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM, max uR uA, max uR uA}
            f).isLeftAdjoint
        (E g).functor.map ((E f).comparison.app Q) ≫
            (E g).comparison.app
              (((ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
                f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Q) ≫
            (extensionOfScalarsComplexComp.{max uR uA, uM} f g).inv.app Q =
          (comp f g).hom.app (DerivedCategory.Q.obj Q) ≫
            (E (g.comp f)).comparison.app Q) ∧
      (∀ {A B C D' : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C] [CommRing D']
          (f : A →+* B) (g : B →+* C) (h : C →+* D')
          (X : DerivedCategory (ModuleCat.{max uR uA uM} A)),
        (E h).functor.map ((comp f g).hom.app X) ≫ (comp (g.comp f) h).hom.app X =
          (comp g h).hom.app ((E f).functor.obj X) ≫
            (comp f (h.comp g)).hom.app X) ∧
      (∀ {A B : Type (max uR uA)} [CommRing A] [CommRing B] (f : A →+* B)
          (X : DerivedCategory (ModuleCat.{max uR uA uM} A)),
        (E f).functor.map ((unit A).hom.app X) ≫
            (comp (RingHom.id A) f).hom.app X = 𝟙 _) ∧
      (∀ {A B : Type (max uR uA)} [CommRing A] [CommRing B] (f : A →+* B)
          (X : DerivedCategory (ModuleCat.{max uR uA uM} A)),
        (unit B).hom.app ((E f).functor.obj X) ≫
            (comp f (RingHom.id B)).hom.app X = 𝟙 _) ∧
      (∀ (K : DerivedCategory (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀))), Plim K →
        ∃ (i : I) (Kᵢ : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i))),
          P i Kᵢ ∧ Nonempty ((S i).functor.obj Kᵢ ≅ K)) ∧
      (∀ (K₀ L₀ : DerivedCategory (ModuleCat.{max uR uA uM} A₀)),
        StacksDraft.PseudoCoherence.IsPseudoCoherent K₀ →
        HasFiniteTorDimension D₀.tensor D₀.comparison D₀.isLeftDerived
            ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀) →
        ∃ (H : I ⥤ Type (max uI uJ (max uR uA uM + 1)))
          (eH : ∀ i : I, H.obj i ≃ ((B i).obj K₀ ⟶ (B i).obj L₀))
          (s : Cocone H)
          (eTarget : s.pt ≃ (Blim.obj K₀ ⟶ Blim.obj L₀))
          (_hs : IsColimit s),
          (∀ {i j : I} (f : i ⟶ j) (x : H.obj i),
            let h : (stageMap F A₀ f).comp (b i) =
                b j := by
              ext a
              simp [b, liftBase, stageMap, baseToStageMap, Algebra.TensorProduct.includeRight_apply,
                Algebra.TensorProduct.map_tmul]
            let stageComp := comp (b i) (stageMap F A₀ f) ≪≫
              derivedExtensionScalarsCongr.{max uR uA, uM} h
            eH j (H.map f x) =
              stageComp.inv.app (W.obj K₀) ≫ (E (stageMap F A₀ f)).functor.map (eH i x) ≫
                stageComp.hom.app (W.obj L₀)) ∧
          (∀ (i : I) (g : (B i).obj K₀ ⟶ (B i).obj L₀),
            let h : (stageToLimitMap c A₀ i).comp (b i) =
                blim := by
              ext a
              simp [b, blim, liftBase, stageToLimitMap, baseToStageMap, baseToLimitMap,
                Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
            let limitComp := comp (b i) (stageToLimitMap c A₀ i) ≪≫
              derivedExtensionScalarsCongr.{max uR uA, uM} h
            eTarget (s.ι.app i ((eH i).symm g)) =
              limitComp.inv.app (W.obj K₀) ≫ (S i).functor.map g ≫ limitComp.hom.app (W.obj L₀))) ∧
      (∀ i : I, (P i).IsTriangulated) ∧ Plim.IsTriangulated ∧
      ∃ (G : I ⥤ Cat.{max uI uJ (max uR uA uM + 1), max uI uJ (max uR uA uM + 1)})
        (eG : ∀ i : I, G.obj i ≌ (P i).FullSubcategory)
        (transition : ∀ {i j : I} (f : i ⟶ j),
          (eG i).inverse ⋙ (G.map f).toFunctor ⋙ (eG j).functor ⋙
              ObjectProperty.ι (P j) ≅
            ObjectProperty.ι (P i) ⋙ (E (stageMap F A₀ f)).functor)
        (_transition_id : ∀ (i : I) (X : (P i).FullSubcategory),
          let mapIdIso : (G.map (𝟙 i)).toFunctor ≅ 𝟭 (G.obj i) :=
            eqToIso (congrArg Cat.Hom.toFunctor (G.map_id i))
          let h : RingHom.id (stageAlgebra F A₀ i) = stageMap F A₀ (𝟙 i) := by
            ext <;> simp [stageMap]
          ((eG i).functor ⋙ ObjectProperty.ι (P i)).map
                (mapIdIso.hom.app ((eG i).inverse.obj X)) ≫
              (ObjectProperty.ι (P i)).map ((eG i).counitIso.hom.app X) ≫
              (unit (stageAlgebra F A₀ i)).hom.app ((ObjectProperty.ι (P i)).obj X) ≫
              (derivedExtensionScalarsCongr.{max uR uA, uM} h).hom.app
                ((ObjectProperty.ι (P i)).obj X) =
            (transition (𝟙 i)).hom.app X)
        (_transition_comp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
            (X : (P i).FullSubcategory),
          let mapCompIso : (G.map (f ≫ g)).toFunctor ≅
              (G.map f).toFunctor ⋙ (G.map g).toFunctor :=
            eqToIso (congrArg Cat.Hom.toFunctor (G.map_comp f g))
          let h : (stageMap F A₀ g).comp (stageMap F A₀ f) =
              stageMap F A₀ (f ≫ g) := by
            ext <;> simp [stageMap, Algebra.TensorProduct.map_tmul]
          let Z := (eG i).inverse.obj X
          let Y := (eG j).functor.obj ((G.map f).toFunctor.obj Z)
          ((eG k).functor ⋙ ObjectProperty.ι (P k)).map (mapCompIso.hom.app Z) ≫
              ((eG k).functor ⋙ ObjectProperty.ι (P k)).map
                ((G.map g).toFunctor.map
                  ((eG j).unitIso.hom.app ((G.map f).toFunctor.obj Z))) ≫
              (transition g).hom.app Y ≫
              (E (stageMap F A₀ g)).functor.map ((transition f).hom.app X) ≫
              (comp (stageMap F A₀ f) (stageMap F A₀ g)).hom.app
                ((ObjectProperty.ι (P i)).obj X) ≫
              (derivedExtensionScalarsCongr.{max uR uA, uM} h).hom.app
                ((ObjectProperty.ι (P i)).obj X) =
            (transition (f ≫ g)).hom.app X)
        (sG : Cocone G) (_hsG : IsColimit sG)
        (eLimit : sG.pt ≌ Plim.FullSubcategory)
        (leg : ∀ i : I,
          (eG i).inverse ⋙ (sG.ι.app i).toFunctor ⋙ eLimit.functor ⋙
                ObjectProperty.ι Plim ≅
            ObjectProperty.ι (P i) ⋙ (S i).functor),
        ∀ {i j : I} (f : i ⟶ j) (X : (P i).FullSubcategory),
          let mapCoconeIso : (G.map f).toFunctor ⋙ (sG.ι.app j).toFunctor ≅
              (sG.ι.app i).toFunctor :=
            eqToIso (congrArg Cat.Hom.toFunctor (sG.w f))
          let h : (stageToLimitMap c A₀ j).comp (stageMap F A₀ f) =
              stageToLimitMap c A₀ i := by
            ext x
            · simp [stageToLimitMap, stageMap]
            · simp [stageToLimitMap, stageMap]
          let limitComp := comp (stageMap F A₀ f) (stageToLimitMap c A₀ j) ≪≫
            derivedExtensionScalarsCongr.{max uR uA, uM} h
          let Z := (eG i).inverse.obj X
          let Y := (eG j).functor.obj ((G.map f).toFunctor.obj Z)
          ((eLimit.functor ⋙ ObjectProperty.ι Plim).map (mapCoconeIso.hom.app Z)) ≫
                (leg i).hom.app X =
            (((sG.ι.app j).toFunctor ⋙ eLimit.functor ⋙ ObjectProperty.ι Plim).map
                ((eG j).unitIso.hom.app ((G.map f).toFunctor.obj Z))) ≫
              (leg j).hom.app Y ≫
              (S j).functor.map ((transition f).hom.app X) ≫
              limitComp.hom.app ((ObjectProperty.ι (P i)).obj X) := by
  classical
  dsimp only
  obtain ⟨comp, hcomp⟩ := exists_derivedExtensionScalarsComp.{max uR uA, uM}
  refine ⟨comp, fun A _ ↦ derivedExtensionScalarsId.{max uR uA, uM} A,
    hcomp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    intro A B C D' _ _ _ _ f g h X
    exact derivedExtensionScalarsComp_assoc comp
      (fun f g P ↦ (hcomp f g P).symm) f g h X
  case refine_2 =>
    intro A B _ _ f X
    exact derivedExtensionScalarsComp_id_left comp
      (fun f g P ↦ (hcomp f g P).symm) f X
  case refine_3 =>
    intro A B _ _ f X
    exact derivedExtensionScalarsComp_id comp
      (fun f g P ↦ (hcomp f g P).symm) f X
  case refine_4 =>
    exact exists_relativelyPerfect_stage.{uI, uJ, uR, uA, uM} F c hc A₀ D Dlim
  case refine_5 =>
    intro K₀ L₀ hK hL
    let W := (ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv.toRingHom : ULift.{uR} A₀ →+* A₀)).mapDerivedCategory
    let H := derivedHomFunctor comp (fun f g P ↦ (hcomp f g P).symm)
      (W.obj K₀) (W.obj L₀)
    let U := CategoryTheory.uliftFunctor.{max uI uJ, max uR uA uM + 1}
    refine ⟨stageUnderFunctor F A₀ ⋙ H ⋙ U, (fun _ ↦ Equiv.ulift),
      U.mapCocone (H.mapCocone (stageUnderCocone c A₀)), Equiv.ulift, ?_, ?_, ?_⟩
    case refine_1 =>
      apply isColimitOfPreserves U
      exact isColimit_stage_derivedHomFunctor.{uI, uJ, uR, uA, uM} comp
        (fun f g P ↦ (hcomp f g P).symm) F c hc A₀ D₀ K₀ L₀ hK hL
    case refine_2 =>
      intro i j f x
      rfl
    case refine_3 =>
      intro i g
      rfl
  case refine_6 =>
    intro i
    exact isTriangulated_relativelyPerfect (A := stageAlgebra F A₀ i) (D i).tensor
      (D i).comparison (D i).isLeftDerived (D i).commShift (D i).triangulated
  case refine_7 =>
    exact isTriangulated_relativelyPerfect (A := c.pt ⊗[R₀] A₀) Dlim.tensor
      Dlim.comparison Dlim.isLeftDerived Dlim.commShift Dlim.triangulated
  case refine_8 =>
    let P (stage : I) : ObjectProperty
        (DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ stage))) :=
      fun object ↦ IsRelativelyPerfect.{uR, max uR uA, uM}
        (R := F.obj stage) (A := stageAlgebra F A₀ stage)
        (D stage).tensor (D stage).comparison (D stage).isLeftDerived object
    let Plim : ObjectProperty
        (DerivedCategory (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀))) :=
      fun object ↦ IsRelativelyPerfect.{uR, max uR uA, uM}
        (R := c.pt) (A := c.pt ⊗[R₀] A₀)
        Dlim.tensor Dlim.comparison Dlim.isLeftDerived object
    let baseWithLimit := WithTerminal.lift F (fun stage ↦ c.ι.app stage)
      (fun _ _ arrow ↦ c.w arrow)
    let ringsWithLimit := stageUnderFunctor baseWithLimit A₀ ⋙
      Under.forget (CommRingCat.of (ULift.{uR} A₀))
    let original := relativelyPerfectLimitPseudofunctor.{uI, uJ, uR, uA, uM}
      comp (fun first second object ↦ (hcomp first second object).symm) F c A₀ D Dlim
    let small := original.comp
      Strictification.smallCatPseudofunctor.{max uI uJ, max uR uA uM + 1, max uR uA uM + 1}
    let diagram := Strictification.terminalRestriction small
    let cone := Strictification.terminalConeData small
    let G := Strictification.strictDiagram diagram
    let eG (stage : I) : G.obj stage ≌ (P stage).FullSubcategory :=
      Strictification.smallTerminalStageEquivalence original stage
    let transition : ∀ {source target : I} (arrow : source ⟶ target),
        (eG source).inverse ⋙ (G.map arrow).toFunctor ⋙ (eG target).functor ⋙
            ObjectProperty.ι (P target) ≅
          ObjectProperty.ι (P source) ⋙
            (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
              (stageMap F A₀ arrow)).functor := fun {source target} arrow ↦
      Functor.isoWhiskerRight (Strictification.smallTerminalTransitionIso original arrow)
        (ObjectProperty.ι (P target))
    let sG := Strictification.strictCocone diagram cone
    have homDescent : Strictification.HomDescent.{uI, uJ, max uR uA uM + 1} diagram cone :=
      { surjective := by
          intro stage source target morphism
          rcases source with ⟨source⟩
          rcases target with ⟨target⟩
          obtain ⟨later, arrow, model, equality⟩ :=
            exists_stageTail_morphism.{uI, uJ, uR, uA, uM} comp
              (fun first second object ↦ (hcomp first second object).symm)
              F c hc A₀ stage (D stage) source.obj target.obj
              source.property.1 target.property.2 (ULift.down morphism).hom
          refine ⟨later, arrow, ULift.up (ObjectProperty.homMk model), ?_⟩
          apply ULift.ext
          conv_lhs =>
            rw [Strictification.smallTerminalLimit_down_comp original]
            arg 2
            rw [Strictification.smallTerminalLimit_down_comp original]
          conv_lhs =>
            arg 1
            rw [Strictification.smallTerminalComparison_inv original arrow source]
          conv_lhs =>
            arg 2
            arg 1
            simp only [Strictification.smallTerminalLeg_down_map original later]
          conv_lhs =>
            arg 2
            arg 2
            rw [Strictification.smallTerminalComparison_hom original arrow target]
          apply ObjectProperty.hom_ext
          conv_lhs =>
            erw [ObjectProperty.FullSubcategory.comp_hom]
            arg 2
            simp only [ObjectProperty.FullSubcategory.comp_hom]
          let ringEquality : (stageToLimitMap c A₀ later).comp (stageMap F A₀ arrow) =
              stageToLimitMap c A₀ stage := RingHom.ext (stageToLimitMap_comp_stageMap c A₀ arrow)
          let comparison := comp (stageMap F A₀ arrow) (stageToLimitMap c A₀ later) ≪≫
            derivedExtensionScalarsCongr.{max uR uA, uM} ringEquality
          let nativeComparison :=
            (Cat.Hom.toNatIso (original.mapComp
              ((WithTerminal.incl : I ⥤ WithTerminal I).map arrow).toLoc
              (WithTerminal.homFrom later).toLoc)).symm
          have identification (object : original.obj ⟨WithTerminal.of stage⟩) :
              (ObjectProperty.ι Plim).mapIso (nativeComparison.app object) =
                comparison.app object.obj := by
            apply Iso.ext
            exact derivedDiagram_mapComp_inv comp
              (fun first second object ↦ (hcomp first second object).symm)
              ringsWithLimit ((WithTerminal.incl : I ⥤ WithTerminal I).map arrow)
              (WithTerminal.homFrom later) object.obj
          show ((ObjectProperty.ι Plim).mapIso (nativeComparison.app source)).inv ≫
              (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
                (stageToLimitMap c A₀ later)).functor.map model ≫
              ((ObjectProperty.ι Plim).mapIso (nativeComparison.app target)).hom =
            (ULift.down morphism).hom
          rw [identification source, identification target]
          exact equality
        eventually_injective := by
          intro stage source target first second equality
          have underlying := congrArg (fun morphism ↦ (ULift.down morphism).hom) equality
          obtain ⟨later, arrow, equality⟩ :=
            exists_stageTail_morphism_equal.{uI, uJ, uR, uA, uM} comp
              (fun first second object ↦ (hcomp first second object).symm)
              F c hc A₀ stage (D stage) (ULift.down source).obj (ULift.down target).obj
              (ULift.down source).property.1 (ULift.down target).property.2 (ULift.down first).hom
                (ULift.down second).hom underlying
          refine ⟨later, arrow, ?_⟩
          apply ULift.ext
          apply ObjectProperty.hom_ext
          exact equality }
    let hsG : IsColimit sG :=
      Strictification.strictCocone_isColimit.{uI, uJ, max uR uA uM + 1} diagram cone
        (Strictification.HomDescent.toMorphismDescent.{uI, uJ, max uR uA uM + 1}
          diagram cone homDescent)
    have objectDescent : ∀ object : small.obj ⟨WithTerminal.star⟩,
        ∃ (stage : I) (model : diagram.obj ⟨stage⟩), Nonempty ((cone.leg stage).obj model ≅
          object) := by
      intro object
      obtain ⟨stage, model, property, ⟨isomorphism⟩⟩ :=
        exists_relativelyPerfect_stage.{uI, uJ, uR, uA, uM}
          F c hc A₀ D Dlim (ULift.down object).obj (ULift.down object).property
      refine ⟨stage, ULift.up ⟨model, property⟩, ⟨?_⟩⟩
      exact AsSmall.up.{max uR uA uM + 1, max uR uA uM + 1, max uI uJ}.mapIso (ObjectProperty.isoMk
        Plim isomorphism)
    let eLimit : sG.pt ≌ Plim.FullSubcategory :=
      (Strictification.limitEquivalence diagram cone objectDescent).trans
        AsSmall.equiv.{max uR uA uM + 1, max uR uA uM + 1, max uI uJ}.symm
    let leg : ∀ stage : I,
        (eG stage).inverse ⋙ (sG.ι.app stage).toFunctor ⋙ eLimit.functor ⋙ ObjectProperty.ι Plim ≅
          ObjectProperty.ι (P stage) ⋙
            (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
              (stageToLimitMap c A₀ stage)).functor := fun stage ↦
      Functor.isoWhiskerRight (Strictification.smallTerminalLegIso original stage)
        (ObjectProperty.ι Plim)
    refine ⟨G, eG, @transition, ?_, ?_, sG, hsG, eLimit, leg, ?_⟩
    · intro stage object
      let identityEquality : RingHom.id (stageAlgebra F A₀ stage) = stageMap F A₀ (𝟙 stage) := by
        ext <;> simp [stageMap]
      have projection : ((original.mapId ⟨WithTerminal.of stage⟩).inv.toNatTrans.app object).hom =
          (derivedExtensionScalarsId.{max uR uA, uM} (stageAlgebra F A₀ stage)).hom.app object.obj ≫
            (derivedExtensionScalarsCongr.{max uR uA, uM} identityEquality).hom.app object.obj := by
        exact derivedDiagram_mapId_inv comp (fun first second object ↦
          (hcomp first second object).symm)
          ringsWithLimit (WithTerminal.of stage) object.obj
      have coherence := Strictification.smallTerminalTransition_id original stage object
      have projected := congrArg (fun morphism ↦ morphism.hom) coherence
      conv_lhs at projected =>
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        rw [projection]
      exact projected
    · intro source middle target first second object
      let compositionEquality : (stageMap F A₀ second).comp (stageMap F A₀ first) =
          stageMap F A₀ (first ≫ second) := by
        ext <;> simp [stageMap, Algebra.TensorProduct.map_tmul]
      have projection : ((original.mapComp
          ((WithTerminal.incl : I ⥤ WithTerminal I).map first).toLoc
          ((WithTerminal.incl : I ⥤ WithTerminal I).map second).toLoc).inv.toNatTrans.app
            object).hom =
          (comp (stageMap F A₀ first) (stageMap F A₀ second)).hom.app object.obj ≫
            (derivedExtensionScalarsCongr.{max uR uA, uM} compositionEquality).hom.app object.obj
              := by
        exact derivedDiagram_mapComp_inv comp (fun first second object ↦
          (hcomp first second object).symm)
          ringsWithLimit ((WithTerminal.incl : I ⥤ WithTerminal I).map first)
          ((WithTerminal.incl : I ⥤ WithTerminal I).map second) object.obj
      have coherence := Strictification.smallTerminalTransition_comp original first second object
      have projected := congrArg (fun morphism ↦ morphism.hom) coherence
      conv_lhs at projected =>
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        rw [projection]
      exact projected
    · intro source target arrow object
      let compositionEquality : (stageToLimitMap c A₀ target).comp (stageMap F A₀ arrow) =
          stageToLimitMap c A₀ source := RingHom.ext (stageToLimitMap_comp_stageMap c A₀ arrow)
      have projection : ((original.mapComp
          ((WithTerminal.incl : I ⥤ WithTerminal I).map arrow).toLoc
          (WithTerminal.homFrom target).toLoc).inv.toNatTrans.app object).hom =
          (comp (stageMap F A₀ arrow) (stageToLimitMap c A₀ target)).hom.app object.obj ≫
            (derivedExtensionScalarsCongr.{max uR uA, uM} compositionEquality).hom.app object.obj
              := by
        exact derivedDiagram_mapComp_inv comp (fun first second object ↦
          (hcomp first second object).symm)
          ringsWithLimit ((WithTerminal.incl : I ⥤ WithTerminal I).map arrow)
          (WithTerminal.homFrom target) object.obj
      have coherence := Strictification.smallTerminalLeg_compatibility original arrow object
      have projected := congrArg (fun morphism ↦ morphism.hom) coherence
      conv_lhs at projected => simp only [ObjectProperty.FullSubcategory.comp_hom]
      conv_rhs at projected =>
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        erw [ObjectProperty.FullSubcategory.comp_hom]
        arg 2
        rw [projection]
      exact projected

end PseudoCoherence

end

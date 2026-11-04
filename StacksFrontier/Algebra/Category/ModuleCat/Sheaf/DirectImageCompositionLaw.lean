module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso

/-!
# The composition law for the direct image of sheaves of modules along morphisms of topoi

Let `φ : E → F` and `ψ : F → G` be morphisms of topoi and let `O` be a sheaf of rings on `G`.
The direct image of sheaves of modules of **Stacks 03D3**,
`Stacks.Sheaves.RingedToposModules.directImageModules`, carries a sheaf of `f⁻¹O`-modules to a
sheaf of `O`-modules; this file identifies the direct image along the composite `ψ ∘ φ` with the
composite of the direct images along `φ` and along `ψ`.

The two composites do not have the same source category. The direct image along `ψ ∘ φ` starts
from sheaves of modules over `(ψ ∘ φ)⁻¹O`, while the iterated direct image starts from sheaves of
modules over `φ⁻¹ψ⁻¹O`, and those are *distinct* sheaves of rings: the underlying sheaf of sets is
the same on the nose, but one carries the ring structure transported along `ψ⁻¹ ⋙ φ⁻¹` in one step
and the other the structure transported along `ψ⁻¹` and then along `φ⁻¹`. The comparison of the
two is `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso`, and the statement below therefore
reads the composite of the direct images after a restriction of scalars along it.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso`: the comparison
  `φ⁻¹ψ⁻¹O ≅ (ψ ∘ φ)⁻¹O` of the two readings of the inverse-image sheaf of rings.
* `Stacks.Sheaves.RingedToposModules.pushforwardRingSheafCompIso`: the comparison
  `ψ_*φ_*S ≅ (ψ ∘ φ)_*S` of the two readings of the direct-image sheaf of rings.
* `Stacks.Sheaves.RingedToposModules.ringUnitComp`: the composite of the two units of Stacks 03D3,
  transported to a map `O ⟶ (ψ ∘ φ)_*(ψ ∘ φ)⁻¹O`.
* `Stacks.Sheaves.RingedToposModules.directImageModulesCompIso`: **the composition law for the
  direct image of sheaves of modules in the morphism variable.**

## Main results

* `Stacks.Sheaves.RingedToposModules.ringUnitComp_eq`: the composite unit is the unit of the
  composite.

## Implementation notes

`iteratedInverseImageRingSheaf`, `iteratedPushforwardRingSheaf`, `directImageModulesCompMid` and
`directImageModulesCompTransportMid` are `abbrev`s naming intermediate objects and functors: with
them inlined, the statement of the composition law exhausts the heartbeat budget at `whnf`.

Each reassociation `(F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H)` is an explicit `CategoryTheory.Functor.associator`,
and each merge of two restrictions of scalars an explicit
`eqToIso (congrArg _ (restrictScalars_comp ..))`. Both are true by `rfl`, but left definitional
they make the kernel unfold `SheafOfModules.restrictScalars` and time out.

The intermediate steps are spelled with `pullbackModuleFunctor`, for which
`pushforwardModuleFunctor` is a semireducible definition; the two spellings are identified once, in
`directImageModulesCompTransportMid_eq`.

The direction of the comparison matches
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` and `MorphismOfTopoi.inverseImageCompIso`:
from the composite of the images to the image of the composite.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Functor Opposite
open CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w w' w'' v u v' u' v'' u''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [L.HasSheafCompose (forget RingCat.{w''})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [L.HasSheafCompose (forget AddCommGrpCat.{w''})]
  (φ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (ψ : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
  (O : Sheaf L RingCat.{w''})

/-! ## The two readings of the transported sheaves of rings -/

/-- The iterated inverse-image sheaf of rings `φ⁻¹ψ⁻¹O`. This is the sheaf of rings the composite
of the two direct images takes its modules over, and it is *not* `(ψ ∘ φ)⁻¹O`: the underlying
sheaf of sets is the same, the transported ring structure is not. -/
abbrev iteratedInverseImageRingSheaf : Sheaf J RingCat.{w} :=
  inverseImageRingSheaf φ (inverseImageRingSheaf ψ O)

/-- The direct-image sheaf of rings the *first* of the two direct images lands over,
`φ_*φ⁻¹ψ⁻¹O`. -/
abbrev iteratedPushforwardRingSheaf : Sheaf K RingCat.{w'} :=
  pushforwardRingSheaf φ (iteratedInverseImageRingSheaf φ ψ O)

/-- **The two readings of the inverse-image sheaf of rings agree.** Taking the inverse image of
`O` along `ψ` and then along `φ` gives the same sheaf of rings as taking it along `ψ ∘ φ`, the
comparison being the identity on underlying sheaves of sets.

This is `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso` for the two inverse images, whose
composite is the inverse image of `MorphismOfTopoi.comp` by definition. -/
def inverseImageRingSheafCompIso :
    iteratedInverseImageRingSheaf φ ψ O ≅ inverseImageRingSheaf (ψ.comp φ) O :=
  pullbackRingSheafCompIso J K φ.inverseImage ψ.inverseImage O

/-- **The two readings of the direct-image sheaf of rings agree.** For a sheaf of rings `S` on the
source, taking the direct image along `φ` and then along `ψ` gives the same sheaf of rings as
taking it along `ψ ∘ φ`, the comparison being the identity on underlying sheaves of sets.

This is `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso` for the two direct images: the
transport of a ring structure along `MorphismOfTopoi.pushforward` is an instance of the same
construction, the direct image preserving finite products because it is a right adjoint. -/
def pushforwardRingSheafCompIso (S : Sheaf J RingCat.{w}) :
    pushforwardRingSheaf ψ (pushforwardRingSheaf φ S) ≅ pushforwardRingSheaf (ψ.comp φ) S :=
  pullbackRingSheafCompIso L K ψ.pushforward φ.pushforward S

/-! ## The composition law for the unit -/

/-- The unit of `ψ`, followed by the direct image under `ψ` of the unit of `φ`, followed by the
comparison of the two readings of the direct-image sheaf of rings. -/
abbrev ringUnitCompAux :
    O ⟶ pushforwardRingSheaf (ψ.comp φ) (iteratedInverseImageRingSheaf φ ψ O) :=
  (ringUnit ψ O ≫ pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O))) ≫
    (pushforwardRingSheafCompIso φ ψ (iteratedInverseImageRingSheaf φ ψ O)).hom

/-- **The composite of the two units of Stacks 03D3.** The unit `O ⟶ ψ_*ψ⁻¹O` of `ψ`, followed by
the direct image under `ψ` of the unit `ψ⁻¹O ⟶ φ_*φ⁻¹ψ⁻¹O` of `φ`, followed by the two ring
comparisons that carry the result to a map `O ⟶ (ψ ∘ φ)_*(ψ ∘ φ)⁻¹O`. -/
abbrev ringUnitComp :
    O ⟶ pushforwardRingSheaf (ψ.comp φ) (inverseImageRingSheaf (ψ.comp φ) O) :=
  ringUnitCompAux φ ψ O ≫
    pushforwardRingMap (ψ.comp φ) (inverseImageRingSheafCompIso φ ψ O).hom

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [L.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- **The unit of a composite is the composite of the units.** The unit
`O ⟶ (ψ ∘ φ)_*(ψ ∘ φ)⁻¹O` of Stacks 03D3 for the composite `ψ ∘ φ` is
`Stacks.Sheaves.RingedToposModules.ringUnitComp`, the unit of `ψ` followed by the direct image
under `ψ` of the unit of `φ`. -/
theorem ringUnitComp_eq : ringUnitComp φ ψ O = ringUnit (ψ.comp φ) O := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦ ?_))
  refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  -- Term position, not `rw`: the two spellings of the transported ring agree only at default
  -- transparency, so a `rw` here leaves a term that is not type-correct.
  have hid : (ψ.comp φ).pushforward.map
        ((sheafCompose J (forget RingCat.{w})).map
          (inverseImageRingSheafCompIso φ ψ O).hom) =
      𝟙 ((ψ.comp φ).pushforward.obj
        (φ.inverseImage.obj (ψ.inverseImage.obj (Sheaf.ringSheaf O)))) :=
    (congrArg (ψ.comp φ).pushforward.map
          (pullbackRingSheafCompIso_hom_ringSheafMap J K φ.inverseImage ψ.inverseImage O)).trans
      ((ψ.comp φ).pushforward.map_id _)
  have houter : ∀ z, (Sheaf.sectionsFunctor L X).map ((ψ.comp φ).pushforward.map
        ((sheafCompose J (forget RingCat.{w})).map
          (inverseImageRingSheafCompIso φ ψ O).hom)) z = z := fun z ↦
    (congrArg (fun m ↦ (Sheaf.sectionsFunctor L X).map m z) hid).trans
      ((Sheaf.sectionsFunctor L X).map_id_apply _ z)
  have hunit : (sheafCompose K (forget RingCat.{w'})).map
        (ringUnit φ (inverseImageRingSheaf ψ O)) =
      φ.adj.unit.app (ψ.inverseImage.obj (Sheaf.ringSheaf O)) :=
    ringSheafMap_ringUnit φ (inverseImageRingSheaf ψ O)
  show (Sheaf.sectionsFunctor L X).map ((ψ.comp φ).pushforward.map
        ((sheafCompose J (forget RingCat.{w})).map (inverseImageRingSheafCompIso φ ψ O).hom))
      ((Sheaf.sectionsFunctor L X).map (ψ.pushforward.map
          ((sheafCompose K (forget RingCat.{w'})).map
            (ringUnit φ (inverseImageRingSheaf ψ O))))
        ((Sheaf.sectionsFunctor L X).map (ψ.adj.unit.app (Sheaf.ringSheaf O)) x)) =
      (Sheaf.sectionsFunctor L X).map ((ψ.comp φ).adj.unit.app (Sheaf.ringSheaf O)) x
  refine (houter _).trans ?_
  rw [hunit]
  refine Eq.trans ((Sheaf.sectionsFunctor L X).map_comp_apply
    (ψ.adj.unit.app (Sheaf.ringSheaf O))
    (ψ.pushforward.map (φ.adj.unit.app (ψ.inverseImage.obj (Sheaf.ringSheaf O)))) x).symm ?_
  exact congrArg (fun m ↦ (Sheaf.sectionsFunctor L X).map m x)
    (Adjunction.comp_unit_app ψ.adj φ.adj (Sheaf.ringSheaf O)).symm

/-! ## The composition law -/

/-- The composite of the two direct images with its restrictions of scalars merged: the transport
of sheaves of modules along `(ψ ∘ φ)_*` over the *iterated* inverse-image sheaf of rings `φ⁻¹ψ⁻¹O`,
restricting scalars along `ringUnitCompAux`. -/
abbrev directImageModulesCompMid :
    SheafOfModules.{w} (iteratedInverseImageRingSheaf φ ψ O) ⥤ SheafOfModules.{w''} O :=
  pullbackModuleFunctor L (ψ.comp φ).pushforward (iteratedInverseImageRingSheaf φ ψ O) ⋙
    SheafOfModules.restrictScalars (ringUnitCompAux φ ψ O)

/-- **Moving the first unit's restriction of scalars out past the second direct image.** The unit
of `φ` restricting scalars, followed by the transport along `ψ_*` and the unit of `ψ` restricting
scalars, is the transport along `ψ_*` of the first direct-image ring, with the two units merged
into one restriction of scalars. -/
def directImageModulesCompMergeInner :
    SheafOfModules.restrictScalars (ringUnit φ (inverseImageRingSheaf ψ O)) ⋙
        (pullbackModuleFunctor L ψ.pushforward (inverseImageRingSheaf ψ O) ⋙
          SheafOfModules.restrictScalars (ringUnit ψ O)) ≅
      pullbackModuleFunctor L ψ.pushforward (iteratedPushforwardRingSheaf φ ψ O) ⋙
        SheafOfModules.restrictScalars
          (ringUnit ψ O ≫ pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O))) :=
  (Functor.associator
        (SheafOfModules.restrictScalars (ringUnit φ (inverseImageRingSheaf ψ O)))
        (pullbackModuleFunctor L ψ.pushforward (inverseImageRingSheaf ψ O))
        (SheafOfModules.restrictScalars (ringUnit ψ O))).symm ≪≫
    isoWhiskerRight
        (pullbackModuleFunctorRestrictScalarsIso L ψ.pushforward
          (ringUnit φ (inverseImageRingSheaf ψ O))).symm
        (SheafOfModules.restrictScalars (ringUnit ψ O)) ≪≫
      Functor.associator
          (pullbackModuleFunctor L ψ.pushforward (iteratedPushforwardRingSheaf φ ψ O))
          (SheafOfModules.restrictScalars
            (pullbackRingSheafMap L ψ.pushforward
              (ringUnit φ (inverseImageRingSheaf ψ O))))
          (SheafOfModules.restrictScalars (ringUnit ψ O)) ≪≫
        eqToIso (congrArg
          (fun G ↦ pullbackModuleFunctor L ψ.pushforward
            (iteratedPushforwardRingSheaf φ ψ O) ⋙ G)
          (restrictScalars_comp (ringUnit ψ O)
            (pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O)))))

/-- **Merging the two direct images.** The composite of the direct image along `φ` and the direct
image along `ψ` is the transport along `(ψ ∘ φ)_*` over the iterated inverse-image sheaf of rings,
restricting scalars along the composite of the two units. -/
def directImageModulesCompMerge :
    directImageModules φ (inverseImageRingSheaf ψ O) ⋙ directImageModules ψ O ≅
      directImageModulesCompMid φ ψ O :=
  Functor.associator
      (pullbackModuleFunctor K φ.pushforward (iteratedInverseImageRingSheaf φ ψ O))
      (SheafOfModules.restrictScalars (ringUnit φ (inverseImageRingSheaf ψ O)))
      (pullbackModuleFunctor L ψ.pushforward (inverseImageRingSheaf ψ O) ⋙
        SheafOfModules.restrictScalars (ringUnit ψ O)) ≪≫
    isoWhiskerLeft
        (pullbackModuleFunctor K φ.pushforward (iteratedInverseImageRingSheaf φ ψ O))
        (directImageModulesCompMergeInner φ ψ O) ≪≫
      (Functor.associator
          (pullbackModuleFunctor K φ.pushforward (iteratedInverseImageRingSheaf φ ψ O))
          (pullbackModuleFunctor L ψ.pushforward (iteratedPushforwardRingSheaf φ ψ O))
          (SheafOfModules.restrictScalars
            (ringUnit ψ O ≫
              pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O))))).symm ≪≫
        isoWhiskerRight
            (pullbackModuleCompIso L K ψ.pushforward φ.pushforward
              (iteratedInverseImageRingSheaf φ ψ O))
            (SheafOfModules.restrictScalars
              (ringUnit ψ O ≫
                pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O)))) ≪≫
          Functor.associator
              (pullbackModuleFunctor L (ψ.comp φ).pushforward
                (iteratedInverseImageRingSheaf φ ψ O))
              (SheafOfModules.restrictScalars
                (pullbackRingSheafCompIso L K ψ.pushforward φ.pushforward
                  (iteratedInverseImageRingSheaf φ ψ O)).hom)
              (SheafOfModules.restrictScalars
                (ringUnit ψ O ≫
                  pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O)))) ≪≫
            eqToIso (congrArg
              (fun G ↦ pullbackModuleFunctor L (ψ.comp φ).pushforward
                (iteratedInverseImageRingSheaf φ ψ O) ⋙ G)
              (restrictScalars_comp
                (ringUnit ψ O ≫
                  pushforwardRingMap ψ (ringUnit φ (inverseImageRingSheaf ψ O)))
                (pushforwardRingSheafCompIso φ ψ
                  (iteratedInverseImageRingSheaf φ ψ O)).hom))

/-- The transport along `(ψ ∘ φ)_*` over `(ψ ∘ φ)⁻¹O`, followed by restriction of scalars along the
comparison of the two inverse-image sheaves of rings and then along `ringUnitCompAux`. -/
abbrev directImageModulesCompTransportMid :
    SheafOfModules.{w} (inverseImageRingSheaf (ψ.comp φ) O) ⥤ SheafOfModules.{w''} O :=
  pullbackModuleFunctor L (ψ.comp φ).pushforward (inverseImageRingSheaf (ψ.comp φ) O) ⋙
    (SheafOfModules.restrictScalars
        (pullbackRingSheafMap L (ψ.comp φ).pushforward
          (inverseImageRingSheafCompIso φ ψ O).hom) ⋙
      SheafOfModules.restrictScalars (ringUnitCompAux φ ψ O))

omit [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [L.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- The two restrictions of scalars of `directImageModulesCompTransportMid` merge into the unit of
the composite, making it the direct image of sheaves of modules along `ψ ∘ φ`. -/
theorem directImageModulesCompTransportMid_eq :
    directImageModulesCompTransportMid φ ψ O = directImageModules (ψ.comp φ) O :=
  (congrArg
        (fun G ↦ pullbackModuleFunctor L (ψ.comp φ).pushforward
          (inverseImageRingSheaf (ψ.comp φ) O) ⋙ G)
        (restrictScalars_comp (ringUnitCompAux φ ψ O)
          (pushforwardRingMap (ψ.comp φ)
            (inverseImageRingSheafCompIso φ ψ O).hom))).trans
    (congrArg
      (fun k ↦ pushforwardModuleFunctor (ψ.comp φ) (inverseImageRingSheaf (ψ.comp φ) O) ⋙
        SheafOfModules.restrictScalars k) (ringUnitComp_eq φ ψ O))

/-- The functor `directImageModulesCompMid`, read on sheaves of modules over `(ψ ∘ φ)⁻¹O` through
the comparison of the two inverse-image sheaves of rings, is the direct image of sheaves of modules
along `ψ ∘ φ`. -/
def directImageModulesCompTransport :
    SheafOfModules.restrictScalars (inverseImageRingSheafCompIso φ ψ O).hom ⋙
        directImageModulesCompMid φ ψ O ≅
      directImageModules (ψ.comp φ) O :=
  (Functor.associator
        (SheafOfModules.restrictScalars (inverseImageRingSheafCompIso φ ψ O).hom)
        (pullbackModuleFunctor L (ψ.comp φ).pushforward
          (iteratedInverseImageRingSheaf φ ψ O))
        (SheafOfModules.restrictScalars (ringUnitCompAux φ ψ O))).symm ≪≫
    isoWhiskerRight
        (pullbackModuleFunctorRestrictScalarsIso L (ψ.comp φ).pushforward
          (inverseImageRingSheafCompIso φ ψ O).hom).symm
        (SheafOfModules.restrictScalars (ringUnitCompAux φ ψ O)) ≪≫
      Functor.associator
          (pullbackModuleFunctor L (ψ.comp φ).pushforward
            (inverseImageRingSheaf (ψ.comp φ) O))
          (SheafOfModules.restrictScalars
            (pullbackRingSheafMap L (ψ.comp φ).pushforward
              (inverseImageRingSheafCompIso φ ψ O).hom))
          (SheafOfModules.restrictScalars (ringUnitCompAux φ ψ O)) ≪≫
        eqToIso (directImageModulesCompTransportMid_eq φ ψ O)

/-- **The direct image of sheaves of modules along a composite of morphisms of topoi is the
composite of the direct images.** For `φ : E → F` and `ψ : F → G` and a sheaf of rings `O` on `G`,
the composite of the direct image along `φ` and the direct image along `ψ` is the direct image
along `ψ ∘ φ`, read on sheaves of modules over `(ψ ∘ φ)⁻¹O` through the restriction of scalars
along the comparison `φ⁻¹ψ⁻¹O ≅ (ψ ∘ φ)⁻¹O` of the two inverse-image sheaves of rings.

The direction is from the composite of the images to the image of the composite, matching
`MorphismOfTopoi.inverseImageCompIso` and
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso`. -/
def directImageModulesCompIso :
    SheafOfModules.restrictScalars (inverseImageRingSheafCompIso φ ψ O).hom ⋙
        directImageModules φ (inverseImageRingSheaf ψ O) ⋙ directImageModules ψ O ≅
      directImageModules (ψ.comp φ) O :=
  isoWhiskerLeft (SheafOfModules.restrictScalars (inverseImageRingSheafCompIso φ ψ O).hom)
      (directImageModulesCompMerge φ ψ O) ≪≫
    directImageModulesCompTransport φ ψ O

end Stacks.Sheaves.RingedToposModules

end

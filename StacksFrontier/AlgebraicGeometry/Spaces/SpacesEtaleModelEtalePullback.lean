module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage

/-!
# Postcomposition with an étale morphism on the spaces-étale models

Let `j : X ⟶ Y` be an étale morphism of algebraic spaces.  Postcomposition `W ↦ (W ⟶ X ⟶ Y)` is a
functor from the spaces-étale site of `X` to that of `Y`, left adjoint to base change along `j`
(Stacks 03LP, 03G2).  This file transports it to the `Type u`-presented models of the ringed
spaces-étale sites, with its structure map (a regular function on `W` is a regular function on
the same algebraic space `W`, read over `Y`), proves the two compatibilities of the structure
maps with the adjunction, and identifies the inverse image of modules along the morphism of
models `AlgebraicGeometry.Space.spacesEtaleModelHom j` with restriction along postcomposition.

## Main definitions

* `AlgebraicGeometry.Space.smallModelPostcomp`: postcomposition on the small models.
* `AlgebraicGeometry.Space.smallModelPostcompAdjunction`: postcomposition is left adjoint to base
  change on the small models.
* `AlgebraicGeometry.Space.smallModelPostcompSharp`: its structure map.

## Main results

* `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_unit_comp_projection` and
  `…_counit_toSpaces`: the unit of postcomposition ⊣ base change is a section of the cartesian
  projection, and its counit is the cartesian projection.
* `AlgebraicGeometry.Space.smallModelPostcomp_H₂`: the structure maps are compatible with the unit.
* `AlgebraicGeometry.Space.smallModelPostcompAdjunction_counit_sharpMap`: the counit, read on
  algebraic spaces, is the morphism along which the structure maps pull back regular functions.
* `AlgebraicGeometry.Space.smallModelPostcomp_H₁_apply`: the structure maps are compatible with
  the counit.
* `AlgebraicGeometry.Space.spacesEtaleModelPullbackIsoPushforward`: the inverse image of modules
  along `AlgebraicGeometry.Space.spacesEtaleModelHom j` is restriction along postcomposition.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (j : X ⟶ Y) (hj : IsEtale B S hS j.hom)

/-- Postcomposition with an étale morphism, transported to the small models. -/
abbrev smallModelPostcomp :
    SmallModel.{u} (SpacesEtale B S hS X) ⥤ SmallModel.{u} (SpacesEtale B S hS Y) :=
  (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse ⋙ spacesEtalePostcomp B S hS j hj ⋙
    (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor

/-- Postcomposition on the small models is continuous. -/
instance isContinuous_smallModelPostcomp : (smallModelPostcomp B S hS j hj).IsContinuous
    (smallModelTopology B S hS X) (smallModelTopology B S hS Y) :=
  have : (spacesEtalePostcomp B S hS j hj ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor).IsContinuous
      (SpacesEtale.topology B S hS X) (smallModelTopology B S hS Y) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _

/-- Postcomposition is left adjoint to base change, on the small models. -/
def smallModelPostcompAdjunction : smallModelPostcomp B S hS j hj ⊣ smallModelBaseChange B S hS j :=
  (equivSmallModel.{u} (SpacesEtale B S hS X)).symm.toAdjunction.comp
    ((spacesEtalePostcompBaseChangeAdjunction B S hS j hj).comp
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).toAdjunction)

/-- The identification of the regular functions on an object of the model of `X` with those on
its postcomposite, through the comparison with the small model of `Y`. -/
def spacesEtalePostcompSharp :
    SpacesEtale.structurePresheaf B S hS X ⟶
      (spacesEtalePostcomp B S hS j hj ⋙ (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse).op ⋙
          SpacesEtale.structurePresheaf B S hS Y :=
  Functor.whiskerRight (NatTrans.op (Functor.whiskerLeft (spacesEtalePostcomp B S hS j hj)
    (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv))
    (SpacesEtale.structurePresheaf B S hS Y)

/-- The structure map of postcomposition on the models, on commutative rings. -/
def smallModelPostcompSharpComm :
    (spacesEtaleModelStructureSheaf B S hS X).obj ⟶
      (smallModelPostcomp B S hS j hj).op ⋙ (spacesEtaleModelStructureSheaf B S hS Y).obj :=
  haveI : ∀ V, Small.{u} (((spacesEtalePostcomp B S hS j hj ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse).op ⋙
          SpacesEtale.structurePresheaf B S hS Y).obj V) := fun _ =>
    small_globalFunctions B S hS _
  Functor.whiskerLeft (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.op
    (shrinkCommRingPresheafMap.{u, u + 1} (spacesEtalePostcompSharp B S hS j hj))

/-- The structure map of postcomposition on the models. -/
def smallModelPostcompSharp :
    Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O ⟶
      ((smallModelPostcomp B S hS j hj).sheafPushforwardContinuous RingCat.{u}
        (smallModelTopology B S hS X) (smallModelTopology B S hS Y)).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS Y).O) :=
  ObjectProperty.homMk (Functor.whiskerRight (smallModelPostcompSharpComm B S hS j hj)
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The unit of postcomposition ⊣ base change is a section of the cartesian projection. -/
theorem spacesEtalePostcompBaseChangeAdjunction_unit_comp_projection (A : SpacesEtale B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map
        ((spacesEtalePostcompBaseChangeAdjunction B S hS j hj).unit.app A) ≫
      (spacesBaseChange B S hS j).projection.app
        ((spacesEtalePostcomp B S hS j hj).obj A) = 𝟙 _ := by
  simp only [SpacesEtale.toSpaces, Functor.id_obj, Functor.comp_obj, ObjectProperty.ι_obj,
    Over.forget_obj, spacesBaseChange, ObjectProperty.lift_obj_obj, Over.pullback_obj_left,
    spacesEtalePostcompBaseChangeAdjunction, Adjunction.restrictFullyFaithful,
    Functor.FullyFaithful.homEquiv, ObjectProperty.liftCompιIso, Iso.refl_symm, Equiv.trans_def,
    Over.mapPullbackAdj, Over.map_obj_left, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_mk,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, Iso.homCongr_apply, Iso.app_inv, Iso.refl_hom,
    Category.comp_id, Iso.refl_inv, Iso.app_hom, NatTrans.id_app, Category.id_comp,
    Functor.comp_map, ObjectProperty.homMk_hom, Over.forget_map, Over.homMk_left]
  exact pullback.lift_fst _ _ _

/-- The counit of postcomposition ⊣ base change is the cartesian projection. -/
theorem spacesEtalePostcompBaseChangeAdjunction_counit_toSpaces (V : SpacesEtale B S hS Y) :
    (SpacesEtale.toSpaces B S hS Y).map
        ((spacesEtalePostcompBaseChangeAdjunction B S hS j hj).counit.app V) =
      (spacesBaseChange B S hS j).projection.app V :=
  rfl

/-- The structure map of postcomposition on the models, read through the shrinking equivalences:
pullback of regular functions along the comparison with the small model of `Y`. -/
theorem smallModelPostcompSharpComm_apply (W : (SmallModel.{u} (SpacesEtale B S hS X))ᵒᵖ)
    (s : (spacesEtaleModelStructureSheaf B S hS X).obj.obj W) :
    Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
          ((smallModelPostcomp B S hS j hj).obj W.unop))))
      (((smallModelPostcompSharpComm B S hS j hj).app W).hom s) =
    ((globalFunctionsPresheaf B S hS).map ((SpacesEtale.toSpaces B S hS Y).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesEtalePostcomp B S hS j hj).obj
            ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop)))).op).hom
      (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop))) s) :=
  (Shrink.ringEquiv _).apply_symm_apply _

/-- On algebraic spaces, the unit of postcomposition ⊣ base change on the models followed by the
two structure maps is the identity. -/
theorem smallModelPostcompAdjunction_unit_sharpMap (W : SmallModel.{u} (SpacesEtale B S hS X)) :
    (SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelPostcompAdjunction B S hS j hj).unit.app W)) ≫
      spacesEtaleModelSharpMap B S hS j ((smallModelPostcomp B S hS j hj).obj W) ≫
        (SpacesEtale.toSpaces B S hS Y).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
            ((spacesEtalePostcomp B S hS j hj).obj
              ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W))) = 𝟙 _ := by
  simp only [smallModelPostcompAdjunction, Adjunction.comp_unit_app, Equivalence.toAdjunction_unit,
    spacesEtaleModelSharpMap, Functor.map_comp, Category.assoc]
  set E := equivSmallModel.{u} (SpacesEtale B S hS X)
  set A := E.inverse.obj W
  set a := (spacesEtalePostcompBaseChangeAdjunction B S hS j hj).unit.app A
  set b := (spacesBaseChange B S hS j).functor.map
    ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unit.app
      ((spacesEtalePostcomp B S hS j hj).obj A))
  have hnat : E.inverse.map (E.functor.map (a ≫ b)) ≫ E.unitIso.inv.app _ =
      E.unitIso.inv.app A ≫ a ≫ b := E.unitIso.inv.naturality (a ≫ b)
  have hW : E.inverse.map (E.symm.unit.app W) ≫ E.unitIso.inv.app A = 𝟙 _ := by
    simp [E, A]
  have key : E.inverse.map (E.symm.unit.app W) ≫ E.inverse.map (E.functor.map a) ≫
      E.inverse.map (E.functor.map b) ≫ E.unitIso.inv.app _ = a ≫ b := by
    have h2 : E.inverse.map (E.functor.map a) ≫ E.inverse.map (E.functor.map b) ≫
        E.unitIso.inv.app _ = E.unitIso.inv.app A ≫ a ≫ b := by
      simpa only [Functor.map_comp, Category.assoc] using hnat
    rw [h2, reassoc_of% hW]
  have key' : (SpacesEtale.toSpaces B S hS X).map (E.inverse.map (E.symm.unit.app W)) ≫
      (SpacesEtale.toSpaces B S hS X).map (E.inverse.map (E.symm.inverse.map a)) ≫
      (SpacesEtale.toSpaces B S hS X).map (E.inverse.map (E.symm.inverse.map b)) ≫
      (SpacesEtale.toSpaces B S hS X).map (E.unitIso.inv.app _) =
        (SpacesEtale.toSpaces B S hS X).map a ≫ (SpacesEtale.toSpaces B S hS X).map b := by
    simp only [← Functor.map_comp]
    exact congrArg _ key
  have hp : (SpacesEtale.toSpaces B S hS X).map b ≫ (spacesBaseChange B S hS j).projection.app
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
        ((smallModelPostcomp B S hS j hj).obj W)) =
      (spacesBaseChange B S hS j).projection.app ((spacesEtalePostcomp B S hS j hj).obj A) ≫
        (SpacesEtale.toSpaces B S hS Y).map ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unit.app
          ((spacesEtalePostcomp B S hS j hj).obj A)) :=
    (spacesBaseChange B S hS j).projection.naturality _
  have hu : (SpacesEtale.toSpaces B S hS Y).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unit.app
          ((spacesEtalePostcomp B S hS j hj).obj A)) ≫
      (SpacesEtale.toSpaces B S hS Y).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesEtalePostcomp B S hS j hj).obj A)) = 𝟙 _ := by
    rw [← Functor.map_comp, Equivalence.unit, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have e1 := congrArg (· ≫ (spacesBaseChange B S hS j).projection.app
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
        ((smallModelPostcomp B S hS j hj).obj W)) ≫
      (SpacesEtale.toSpaces B S hS Y).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesEtalePostcomp B S hS j hj).obj A))) key'
  simp only [Category.assoc] at e1
  refine e1.trans ?_
  have e2 := congrArg ((SpacesEtale.toSpaces B S hS X).map a ≫ ·) (congrArg (· ≫
      (SpacesEtale.toSpaces B S hS Y).map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesEtalePostcomp B S hS j hj).obj A))) hp)
  simp only [Category.assoc] at e2
  refine e2.trans ?_
  rw [hu]
  exact (Category.comp_id _).trans
    (spacesEtalePostcompBaseChangeAdjunction_unit_comp_projection B S hS j hj A)

/-- **The second compatibility of the structure maps with the adjunction**: the structure map of
postcomposition, followed by that of base change and restriction along the unit, is the identity.
-/
theorem smallModelPostcomp_H₂ :
    (smallModelPostcompSharp B S hS j hj).hom ≫
      (smallModelPostcomp B S hS j hj).op.whiskerLeft
          (spacesEtaleModelHom B S hS j).fSharpRing.hom ≫
        Functor.whiskerRight (NatTrans.op (smallModelPostcompAdjunction B S hS j hj).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O).obj =
      𝟙 _ := by
  refine NatTrans.ext (funext fun W => ?_)
  refine RingCat.hom_ext (RingHom.ext fun s => ?_)
  apply (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
    (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop)))).injective
  have h1 := smallModelPostcompSharpComm_apply B S hS j hj W s
  have h2 := spacesEtaleModelHom_fSharp_apply B S hS j
    (op ((smallModelPostcomp B S hS j hj).obj W.unop))
    (((smallModelPostcompSharpComm B S hS j hj).app W).hom s)
  have h3 := spacesEtaleModelStructureSheaf_map_apply B S hS X
    ((smallModelPostcompAdjunction B S hS j hj).unit.app W.unop).op
    (((spacesEtaleModelHom B S hS j).fSharp.hom.app
      (op ((smallModelPostcomp B S hS j hj).obj W.unop))).hom
      (((smallModelPostcompSharpComm B S hS j hj).app W).hom s))
  have h4 : ∀ t, (globalFunctionsMap B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelPostcompAdjunction B S hS j hj).unit.app W.unop)) ≫
      spacesEtaleModelSharpMap B S hS j ((smallModelPostcomp B S hS j hj).obj W.unop) ≫
        (SpacesEtale.toSpaces B S hS Y).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
            ((spacesEtalePostcomp B S hS j hj).obj
              ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop))))) t = t := by
    intro t
    refine (congrArg (fun m => globalFunctionsMap B S hS m t)
      (smallModelPostcompAdjunction_unit_sharpMap B S hS j hj W.unop)).trans ?_
    exact congrArg (fun φ : _ →+* _ => φ t) (globalFunctionsMap_id B S hS _)
  have h5 := h4 (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
      (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop))) s)
  rw [globalFunctionsMap_comp, globalFunctionsMap_comp] at h5
  simp only [Opposite.unop_op] at h2 h3
  refine h3.trans ?_
  refine (congrArg (fun t => ((SpacesEtale.structurePresheaf B S hS X).map
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelPostcompAdjunction B S hS j hj).unit.app W.unop)).op).hom t) h2).trans ?_
  refine (congrArg (fun t => ((SpacesEtale.structurePresheaf B S hS X).map
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelPostcompAdjunction B S hS j hj).unit.app W.unop)).op).hom
      (((globalFunctionsPresheaf B S hS).map (spacesEtaleModelSharpMap B S hS j
        ((smallModelPostcomp B S hS j hj).obj W.unop)).op).hom t)) h1).trans ?_
  exact h5

/-- On algebraic spaces, the counit of postcomposition ⊣ base change on the models is the
comparison with the small model followed by the structure map of the base change. -/
theorem smallModelPostcompAdjunction_counit_sharpMap (V : SmallModel.{u} (SpacesEtale B S hS Y)) :
    (SpacesEtale.toSpaces B S hS Y).map ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.map
        ((smallModelPostcompAdjunction B S hS j hj).counit.app V)) =
      (SpacesEtale.toSpaces B S hS Y).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
            ((spacesEtalePostcomp B S hS j hj).obj
              ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
                ((smallModelBaseChange B S hS j).obj V)))) ≫
        spacesEtaleModelSharpMap B S hS j V := by
  set E := equivSmallModel.{u} (SpacesEtale B S hS Y)
  set k := (spacesEtalePostcomp B S hS j hj).map
      ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv.app
        ((spacesBaseChange B S hS j).functor.obj (E.inverse.obj V))) ≫
    (spacesEtalePostcompBaseChangeAdjunction B S hS j hj).counit.app (E.inverse.obj V)
  have hc : (smallModelPostcompAdjunction B S hS j hj).counit.app V =
      E.functor.map k ≫ E.counit.app V := by
    simp [smallModelPostcompAdjunction, k, E]
  have key : E.inverse.map ((smallModelPostcompAdjunction B S hS j hj).counit.app V) =
      E.unitInv.app _ ≫ k := by
    rw [hc, Functor.map_comp, E.inv_fun_map]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (k ≫ ·) (E.unit_inverse_comp V)).trans (Category.comp_id k)
  rw [key]
  refine ((SpacesEtale.toSpaces B S hS Y).map_comp _ _).trans ?_
  exact congrArg (_ ≫ ·) ((SpacesEtale.toSpaces B S hS Y).map_comp _ _)

/-- **The first compatibility of the structure maps with the adjunction**, elementwise through the
shrinking equivalences: restricting a regular function on `V` along the counit is pulling it back
by the structure map of the base change and then by that of postcomposition. -/
theorem smallModelPostcomp_H₁_apply (V : (SmallModel.{u} (SpacesEtale B S hS Y))ᵒᵖ)
    (s : (spacesEtaleModelStructureSheaf B S hS Y).obj.obj V) :
    Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
          ((smallModelPostcomp B S hS j hj).obj ((smallModelBaseChange B S hS j).obj V.unop)))))
      (((spacesEtaleModelStructureSheaf B S hS Y).obj.map
        ((smallModelPostcompAdjunction B S hS j hj).counit.app V.unop).op).hom s) =
    Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj
          ((smallModelPostcomp B S hS j hj).obj ((smallModelBaseChange B S hS j).obj V.unop)))))
      (((smallModelPostcompSharpComm B S hS j hj).app
          (op ((smallModelBaseChange B S hS j).obj V.unop))).hom
        (((spacesEtaleModelHom B S hS j).fSharp.hom.app V).hom s)) := by
  have h1 := spacesEtaleModelStructureSheaf_map_apply B S hS Y
    ((smallModelPostcompAdjunction B S hS j hj).counit.app V.unop).op s
  have h2 := smallModelPostcompSharpComm_apply B S hS j hj
    (op ((smallModelBaseChange B S hS j).obj V.unop))
    (((spacesEtaleModelHom B S hS j).fSharp.hom.app V).hom s)
  have h3 := spacesEtaleModelHom_fSharp_apply B S hS j V s
  simp only [Opposite.unop_op] at h1 h2
  rw [h3] at h2
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (RingHom.congr_fun (congrArg (globalFunctionsMap B S hS)
    (smallModelPostcompAdjunction_counit_sharpMap B S hS j hj V.unop)) _).trans
    (RingHom.congr_fun (globalFunctionsMap_comp B S hS _ _) _)

/-- Postcomposition on the small models is continuous, for the topology of the model of `X` read
on its ringed topos. -/
instance isContinuous_smallModelPostcomp_ringedTopos_left :
    @Functor.IsContinuous _ (spacesEtaleModelRingedTopos B S hS X).category _ _
      (smallModelPostcomp B S hS j hj) (spacesEtaleModelRingedTopos B S hS X).J
      (smallModelTopology B S hS Y) :=
  isContinuous_smallModelPostcomp B S hS j hj

/-- Postcomposition on the small models is continuous, for the topology of the model of `X` read
on its ringed topos (with the category structure of the small model). -/
instance isContinuous_smallModelPostcomp_ringedTopos_topology :
    (smallModelPostcomp B S hS j hj).IsContinuous (spacesEtaleModelRingedTopos B S hS X).J
      (smallModelTopology B S hS Y) :=
  isContinuous_smallModelPostcomp B S hS j hj

/-- Postcomposition on the small models is continuous, for the topologies of the models read on
their ringed topoi. -/
instance isContinuous_smallModelPostcomp_ringedTopos :
    @Functor.IsContinuous _ (spacesEtaleModelRingedTopos B S hS X).category _
      (spacesEtaleModelRingedTopos B S hS Y).category
      (smallModelPostcomp B S hS j hj) (spacesEtaleModelRingedTopos B S hS X).J
      (spacesEtaleModelRingedTopos B S hS Y).J :=
  isContinuous_smallModelPostcomp B S hS j hj

/-- Base change on the small models is continuous, for the topology of the model of `X` read on
its ringed topos. -/
instance isContinuous_smallModelBaseChange_ringedTopos_right :
    (smallModelBaseChange B S hS j).IsContinuous (smallModelTopology B S hS Y)
      (spacesEtaleModelRingedTopos B S hS X).J :=
  isContinuous_smallModelBaseChange B S hS j

/-- **Restriction along postcomposition is left adjoint to the direct image** along the morphism
of models `AlgebraicGeometry.Space.spacesEtaleModelHom j`, induced by postcomposition ⊣ base
change. -/
def smallModelPostcompPushforwardAdjunction :
    SheafOfModules.pushforward (smallModelPostcompSharp B S hS j hj) ⊣
      (spacesEtaleModelHom B S hS j).pushforwardTopos :=
  SheafOfModules.pushforwardPushforwardAdj (smallModelPostcompAdjunction B S hS j hj)
    (smallModelPostcompSharp B S hS j hj) (spacesEtaleModelHom B S hS j).fSharpRing
    (NatTrans.ext (funext fun V => RingCat.hom_ext (RingHom.ext fun s =>
      (Shrink.ringEquiv _).injective (smallModelPostcomp_H₁_apply B S hS j hj V s))))
    (smallModelPostcomp_H₂ B S hS j hj)

/-- **The inverse image of modules along an étale morphism is restriction along
postcomposition**, on the spaces-étale models (Stacks 03LP, 03G2): the inverse image along
`AlgebraicGeometry.Space.spacesEtaleModelHom j` and restriction along postcomposition with `j`
are both left adjoint to the direct image. -/
def spacesEtaleModelPullbackIsoPushforward :
    (spacesEtaleModelHom B S hS j).pullbackTopos ≅
      SheafOfModules.pushforward (smallModelPostcompSharp B S hS j hj) :=
  (spacesEtaleModelHom B S hS j).pullbackPushforwardAdjunctionTopos.leftAdjointUniq
    (smallModelPostcompPushforwardAdjunction B S hS j hj)

end AlgebraicGeometry.Space

end

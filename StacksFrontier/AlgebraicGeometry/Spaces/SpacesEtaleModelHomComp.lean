module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSmallModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi

/-!
# Composition of the morphisms of spaces-étale models

A morphism `f : X ⟶ Y` of algebraic spaces induces the morphism
`AlgebraicGeometry.Space.spacesEtaleModelHom f` of the `Type u`-presented models of the ringed
spaces-étale sites: base change `V ↦ V ×_Y X` on the sites and pullback of regular functions along
the cartesian projections on the structure sheaves.  This file shows that these morphisms compose
up to canonical isomorphism, on direct images, on inverse images and on derived pullbacks: for
`f : X ⟶ Y` and `g : Y ⟶ Z`,

`L(f ≫ g)^* ≅ Lf^* ∘ Lg^*`.

The base-change functors compose by Stacks 03G2, part (2); the structure maps are compatible with
that isomorphism because both pull a regular function back along the same morphism of algebraic
spaces (`AlgebraicGeometry.Space.spacesEtaleModelSharpMap_comp`); the derived statement is then
Stacks 0D6D for the composite of the two morphisms of models.

## Main definitions

* `AlgebraicGeometry.Space.smallModelBaseChangeComp`: the composition isomorphism of the
  base-change functors of the models.
* `AlgebraicGeometry.Space.spacesEtaleModelPushforwardCompIso`,
  `AlgebraicGeometry.Space.spacesEtaleModelPullbackCompIso`: direct and inverse images along the
  morphism of models of `f ≫ g` are those along the composite morphism of models.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`: **`Lf^* ∘ Lg^* ≅ L(f ≫ g)^*`
  on the models.**

## Main results

* `AlgebraicGeometry.Space.fSharpRing_smallModelBaseChangeComp`: the structure maps are compatible
  with the composition isomorphism of the base changes.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Base change on the models composes**: the base change along `g` followed by the base change
along `f`, on the small models of the spaces-étale sites, is the base change along `f ≫ g`.  This
is the composition isomorphism of Stacks 03G2, part (2), transported to the small models. -/
def smallModelBaseChangeComp :
    smallModelBaseChange B S hS g ⋙ smallModelBaseChange B S hS f ≅
      smallModelBaseChange B S hS (f ≫ g) :=
  NatIso.ofComponents (fun V =>
    (equivSmallModel.{u} (SpacesEtale B S hS X)).functor.mapIso
      ((spacesBaseChange B S hS f).functor.mapIso
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.app _).symm ≪≫
        (spacesBaseChange_comp B S hS f g).app _)) (by
    intro V W k
    have h1 := (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.naturality
      ((spacesBaseChange B S hS g).functor.map
        ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.map k))
    have h2 := (spacesBaseChange_comp B S hS f g).hom.naturality
      ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.map k)
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2
    dsimp [smallModelBaseChange]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, h2])

/-- The morphism of algebraic spaces along which the structure map of
`AlgebraicGeometry.Space.spacesEtaleModelHom` pulls back regular functions over an object `V` of
the model: the comparison of the base change `V ×_Y X` with its image in the small model,
followed by the cartesian projection to `V`. -/
def spacesEtaleModelSharpMap {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (V : SmallModel.{u} (SpacesEtale B S hS Y)) :
    (SpacesEtale.toSpaces B S hS X).obj ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
        ((smallModelBaseChange B S hS f).obj V)) ⟶
      (SpacesEtale.toSpaces B S hS Y).obj
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj V) :=
  (SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv.app
      ((spacesBaseChange B S hS f).functor.obj
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj V))) ≫
    (spacesBaseChange B S hS f).projection.app
      ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj V)

/-- The structure map of `AlgebraicGeometry.Space.spacesEtaleModelHom` over `V`, read through the
shrinking equivalences: pullback of regular functions along
`AlgebraicGeometry.Space.spacesEtaleModelSharpMap`. -/
theorem spacesEtaleModelHom_fSharp_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (V : (SmallModel.{u} (SpacesEtale B S hS Y))ᵒᵖ)
    (s : (spacesEtaleModelStructureSheaf B S hS Y).obj.obj V) :
    Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
          ((smallModelBaseChange B S hS f).obj V.unop))))
        (((spacesEtaleModelHom B S hS f).fSharp.hom.app V).hom s) =
      ((globalFunctionsPresheaf B S hS).map (spacesEtaleModelSharpMap B S hS f V.unop).op).hom
        (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Y).obj
          (op ((equivSmallModel.{u} (SpacesEtale B S hS Y)).inverse.obj V.unop))) s) := by
  refine ((Shrink.ringEquiv _).apply_symm_apply _).trans ?_
  rw [spacesEtaleModelSharpMap, op_comp, Functor.map_comp]
  rfl

/-- The restriction maps of the structure sheaf of the model, read through the shrinking
equivalences: pullback of regular functions. -/
theorem spacesEtaleModelStructureSheaf_map_apply (X : AlgebraicSpaces B S hS)
    {V W : (SmallModel.{u} (SpacesEtale B S hS X))ᵒᵖ} (h : V ⟶ W)
    (s : (spacesEtaleModelStructureSheaf B S hS X).obj.obj V) :
    Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
        (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj W.unop)))
        (((spacesEtaleModelStructureSheaf B S hS X).obj.map h).hom s) =
      ((SpacesEtale.structurePresheaf B S hS X).map
        ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map h.unop).op).hom
        (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
          (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj V.unop))) s) :=
  (Shrink.ringEquiv _).apply_symm_apply _

/-- The morphisms along which the structure maps pull back regular functions compose: over an
object `V` of the model of `Z`, the morphism for `f ≫ g`, read through the composition isomorphism
of the base changes, is the morphism for `f` over the base change of `V` followed by the morphism
for `g`. -/
theorem spacesEtaleModelSharpMap_comp (V : SmallModel.{u} (SpacesEtale B S hS Z)) :
    (SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelBaseChangeComp B S hS f g).hom.app V)) ≫
        spacesEtaleModelSharpMap B S hS (f ≫ g) V =
      spacesEtaleModelSharpMap B S hS f ((smallModelBaseChange B S hS g).obj V) ≫
        spacesEtaleModelSharpMap B S hS g V := by
  have hu := (equivSmallModel.{u} (SpacesEtale B S hS X)).unitIso.inv.naturality
    ((spacesBaseChange B S hS f).functor.map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesBaseChange B S hS g).functor.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V))) ≫
      (spacesBaseChange_comp B S hS f g).hom.app
        ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V))
  have hp : (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange B S hS f).functor.map
        ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
          ((spacesBaseChange B S hS g).functor.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V)))) ≫
        (spacesBaseChange B S hS f).projection.app
          ((spacesBaseChange B S hS g).functor.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V)) =
      (spacesBaseChange B S hS f).projection.app _ ≫
        (SpacesEtale.toSpaces B S hS Y).map
          ((equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.app
            ((spacesBaseChange B S hS g).functor.obj
              ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V))) :=
    (spacesBaseChange B S hS f).projection.naturality _
  have hc : (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChange_comp B S hS f g).hom.app
        ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V)) ≫
        (spacesBaseChange B S hS (f ≫ g)).projection.app
          ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V) =
      (spacesBaseChange B S hS f).projection.app
          ((spacesBaseChange B S hS g).functor.obj
            ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V)) ≫
        (spacesBaseChange B S hS g).projection.app
          ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V) :=
    spacesBaseChange_comp_projection B S hS f g _
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu
  simp only [spacesEtaleModelSharpMap, smallModelBaseChangeComp, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc, Functor.map_comp_assoc, hc]
  slice_lhs 2 3 => rw [hp]
  simp only [Category.assoc]
  rfl

/-- The composite of the base-change functors of the models is continuous. -/
instance isContinuous_smallModelBaseChange_comp :
    (smallModelBaseChange B S hS g ⋙ smallModelBaseChange B S hS f).IsContinuous
    (smallModelTopology B S hS Z) (smallModelTopology B S hS X) :=
  Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Y) _

/-- **The structure maps of the morphisms of models compose**: the structure map of the morphism of
models of `f ≫ g`, read through the composition isomorphism of the base changes, is the structure
map of the composite of the morphisms of models of `f` and of `g`. -/
theorem fSharpRing_smallModelBaseChangeComp :
    (spacesEtaleModelHom B S hS (f ≫ g)).fSharpRing ≫
      (Functor.sheafPushforwardContinuousNatTrans (smallModelBaseChangeComp B S hS f g).hom
        RingCat.{u} (smallModelTopology B S hS Z) (smallModelTopology B S hS X)).app _ =
      ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f)).fSharpRing := by
  ext V s
  apply (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
    (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj
      ((smallModelBaseChange B S hS f).obj
        ((smallModelBaseChange B S hS g).obj V.unop)))))).injective
  have h1 := spacesEtaleModelStructureSheaf_map_apply B S hS X
    ((smallModelBaseChangeComp B S hS f g).hom.app V.unop).op
    (((spacesEtaleModelHom B S hS (f ≫ g)).fSharp.hom.app V).hom s)
  have h2 := spacesEtaleModelHom_fSharp_apply B S hS (f ≫ g) V s
  have h3 := spacesEtaleModelHom_fSharp_apply B S hS g V s
  have h4 := spacesEtaleModelHom_fSharp_apply B S hS f
    (op ((smallModelBaseChange B S hS g).obj V.unop))
    (((spacesEtaleModelHom B S hS g).fSharp.hom.app V).hom s)
  have h5 := congrArg (fun m => ((globalFunctionsPresheaf B S hS).map m.op).hom
    (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS Z).obj
      (op ((equivSmallModel.{u} (SpacesEtale B S hS Z)).inverse.obj V.unop))) s))
    (spacesEtaleModelSharpMap_comp B S hS f g V.unop)
  simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h5
  refine h1.trans ?_
  rw [h2]
  refine Eq.trans ?_ h4.symm
  rw [h3]
  exact h5

/-- **Direct images along the morphisms of models compose.**  The direct image of modules along
the morphism of models of `f ≫ g` is the direct image along the composite of the morphisms of
models of `f` and of `g`. -/
def spacesEtaleModelPushforwardCompIso :
    (spacesEtaleModelHom B S hS (f ≫ g)).pushforwardTopos ≅
      ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f)).pushforwardTopos :=
  SheafOfModules.pushforwardCongr₂ _ (smallModelBaseChangeComp B S hS f g)
    (fSharpRing_smallModelBaseChangeComp B S hS f g)

/-- **Inverse images along the morphisms of models compose**, by uniqueness of left adjoints. -/
def spacesEtaleModelPullbackCompIso :
    (spacesEtaleModelHom B S hS (f ≫ g)).pullbackTopos ≅
      ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f)).pullbackTopos :=
  ((spacesEtaleModelHom B S hS (f ≫ g)).pullbackPushforwardAdjunctionTopos).leftAdjointUniq
    ((((spacesEtaleModelHom B S hS g).comp
      (spacesEtaleModelHom B S hS f)).pullbackPushforwardAdjunctionTopos).ofNatIsoRight
        (spacesEtaleModelPushforwardCompIso B S hS f g).symm)

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

/-- The derived pullback along the morphism of models induced by a morphism of algebraic spaces
exists: the underlying functor of sites is a morphism of sites. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_spacesEtaleModelHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (pullbackOnHomotopy (spacesEtaleModelHom B S hS f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS Y).O)) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (spacesEtaleModelHom B S hS f)
    (isMorphismOfSites_spacesEtaleModelHom B S hS f)

/-- **Derived pullbacks along the morphisms of models compose** (Stacks 0D6D on the models):
`Lf^* ∘ Lg^* ≅ L(f ≫ g)^*`. -/
def spacesEtaleModelDerivedPullbackCompIso :
    derivedPullback (spacesEtaleModelHom B S hS g) ⋙
        derivedPullback (spacesEtaleModelHom B S hS f) ≅
      derivedPullback (spacesEtaleModelHom B S hS (f ≫ g)) :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    ((spacesEtaleModelHom B S hS g).comp (spacesEtaleModelHom B S hS f))
    ((isMorphismOfSites_spacesEtaleModelHom B S hS g).comp
      (isMorphismOfSites_spacesEtaleModelHom B S hS f))
  derivedPullbackCompIso (spacesEtaleModelHom B S hS f) (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS f)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g) ≪≫
    (derivedPullbackIsoOfPullbackIso _ _ (spacesEtaleModelPullbackCompIso B S hS f g)).symm

end AlgebraicGeometry.Space

end

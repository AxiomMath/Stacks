module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperSurjectiveDescent
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsMateTerminal
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

/-!
# Sections of `π_X⁻¹F` as morphisms of small étale sheaves

Let `E` be a big étale site of algebraic spaces over a scheme `S`, `X` an algebraic space of it,
`π_X` the morphism from the big étale topos of `X` to its small étale topos (Stacks 0DF3) and `F`
a sheaf of sets on the spaces-étale site of `X`. For `f : Y ⟶ X`, the sections of `π_X⁻¹F` over
`f` are the global sections of `f⁻¹F` (Stacks 0DG7), i.e. the morphisms `f⁻¹⊤ ⟶ f⁻¹F` of small
étale sheaves on `Y`. This file proves that these identifications are compatible with restriction
along *every* morphism of the slice over `X`, not only étale ones. Consequently `π_X⁻¹F` is the
presheaf of morphisms `T ↦ (T⁻¹⊤ ⟶ T⁻¹F)` of the pseudofunctor of spaces-étale inverse images, and
full faithfulness of descent along a morphism (the prestack condition) gives the sheaf condition
of `π_X⁻¹F` for that morphism. With 0DGX's descent along proper surjections this is
proper-surjective descent for `π_X⁻¹F`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.sectionsIso`: the section rule, as an isomorphism of
  functors of `F`.
* `AlgebraicGeometry.BigEtaleSpaceSite.homEquivSections`: morphisms `f⁻¹⊤ ⟶ f⁻¹F` are sections of
  `π_X⁻¹F` over `f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.presheafHomIso`: the presheaf of morphisms from the
  terminal sheaf to `F`, for the pseudofunctor of spaces-étale inverse images, is `π_X⁻¹F`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.sectionsIso_restriction` and
  `AlgebraicGeometry.BigEtaleSpaceSite.homEquivSections_naturality`: compatibility with
  restriction along any morphism.
* `AlgebraicGeometry.BigEtaleSpaceSite.isSheafFor_inverseImage_singleton_of_isPrestackFor`:
  the prestack condition along `f.left` gives the sheaf condition of `π_X⁻¹F` for `f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.isSheafFor_inverseImage_of_isProper_isSurjective`:
  `π_X⁻¹F` satisfies descent along every proper surjective morphism of the slice, granted
  `AlgebraicGeometry.Space.ProperSurjectivePrestackOverSchemes`.

## References

* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) {X : E.Spaces}

/-- Base change of spaces-étale sites is continuous, being a morphism of sites (Stacks 03G2). -/
local instance spacesBaseChangeContinuous {X Y : E.Spaces} (f : X ⟶ Y) :
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.IsContinuous
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) :=
  (Space.spacesBaseChange_isMorphismOfSites E.fppfSite S E.fppf_mem f).isContinuous

/-- The direct image along base change has the spaces-étale inverse image as left adjoint. -/
local instance spacesBaseChangeRightAdjoint {X Y : E.Spaces} (f : X ⟶ Y) :
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPushforwardContinuous
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)).IsRightAdjoint :=
  (Space.spacesEtaleAdjunction E.fppfSite S E.fppf_mem f).isRightAdjoint

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the limits of the pointwise right Kan extension is deep
/-- Right Kan extensions along the inclusion `i_f` of Stacks 0DF2 exist pointwise: the
relevant limits are indexed by categories of the size of the site. -/
local instance inclusionFunctorPointwiseRan {Y : E.Spaces} (f : Y ⟶ X)
    (F : (Space.SpacesEtale E.fppfSite S E.fppf_mem Y)ᵒᵖ ⥤ Type (u + 1)) :
    (inclusionFunctor E f).op.HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- Each projection `V ×_X Y ⟶ V` of `AlgebraicGeometry.BigEtaleSpaceSite.inclusionTransition`
is initial among the structured arrows over `i_g`: this is the universal property of the fibre
product. -/
def inclusionTransitionInitial {Y : E.Spaces} (g : Y ⟶ X)
    (U : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    IsInitial (StructuredArrow.mk (T := (inclusionFunctor E g).op)
      ((inclusionTransition E g).app U).op) := by
  let b := Space.spacesBaseChange E.fppfSite S E.fppf_mem g
  have hpb := b.isPullback U
  let lift (k : StructuredArrow
      (op ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X).obj U))
      (inclusionFunctor E g).op) : k.right.unop ⟶ b.functor.obj U :=
    ObjectProperty.homMk (Over.homMk (hpb.lift k.hom.unop.left k.right.unop.1.hom
      (Over.w k.hom.unop)) (hpb.lift_snd _ _ _))
  refine IsInitial.ofUniqueHom (fun k => StructuredArrow.homMk (lift k).op ?_) ?_
  · exact Quiver.Hom.unop_inj (Over.OverMorphism.ext (hpb.lift_fst _ _ _))
  · intro k m
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    have hm := congrArg (fun z => Over.Hom.left (Quiver.Hom.unop z)) (StructuredArrow.w m)
    change m.right.unop.hom.left ≫ b.projection.app U = k.hom.unop.left at hm
    apply hpb.hom_ext
    · exact hm.trans (hpb.lift_fst _ _ _).symm
    · exact (Over.w m.right.unop.hom).trans (hpb.lift_snd _ _ _).symm

/-- The small étale pullback along `f : Y ⟶ X` is `π_X⁻¹` followed by restriction along the
inclusion `i_f` of Stacks 0DF2. -/
def smallPullbackIso {Y : E.Spaces} (f : Y ⟶ X) :
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) ≅
      (E.bigToSmallEtaleMorphism X).inverseImage ⋙
        (inclusionFunctor E f).sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (E.bigEtaleTopology X) :=
  sheafPullbackIsoOfInitial (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (E.bigEtaleTopology X)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (inclusionFunctor E f) (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X)
    (inclusionTransition E f) (E.bigToSmallEtaleMorphism X).inverseImage
    (E.bigToSmallEtaleMorphism X).adj (inclusionTransitionInitial E f)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the sheaf pullback and sections of the spaces étale sites is deep
/-- **The section rule of Stacks 0DG7**: the sections of `π_X⁻¹F` over `f : Y ⟶ X` are the
global sections of `f⁻¹F`, naturally in `F`. -/
def sectionsIso {Y : E.Spaces} (f : Y ⟶ X) :
    (E.bigToSmallEtaleMorphism X).inverseImage ⋙
        (sheafSections (E.bigEtaleTopology X) (Type (u + 1))).obj (op (Over.mk f)) ≅
      (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) ⋙
        Sheaf.Γ (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (Type (u + 1)) :=
  sheafPullbackSectionsIso (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (E.bigEtaleTopology X)
    (inclusionFunctor E f) (E.bigToSmallEtaleMorphism X).inverseImage _
    (smallPullbackIso E f) (Space.SpacesEtale.isTerminal_idObj E.fppfSite S E.fppf_mem Y)

/-- The canonical map `Γ(Y, f⁻¹F) ⟶ Γ(Z, (h ≫ f)⁻¹F)` for `h : Z ⟶ Y`: the unit of `h⁻¹ ⊣ h_*`
followed by the composition isomorphism of base changes, at the final object. -/
def sectionsRestriction {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :=
  sheafPullbackSectionsRestriction (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor
    (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f)
    (Space.SpacesEtale.isTerminal_idObj E.fppfSite S E.fppf_mem Y)
    (Space.isTerminal_spacesBaseChange_idObj E.fppfSite S E.fppf_mem h) F

/-- The projections `V ×_Y Z ⟶ V` and `V ×_X Y ⟶ V` are compatible with the composition
isomorphism of base changes (Stacks 03G2, part (2)). -/
theorem inclusionFunctorTransition_comp {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (U : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (inclusionFunctorTransition E h f).app
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.obj U) ≫
      (inclusionTransition E f).app U =
    (inclusionFunctor E (h ≫ f)).map
        ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).hom.app U) ≫
      (inclusionTransition E (h ≫ f)).app U :=
  Over.OverMorphism.ext (Space.spacesBaseChange_comp_projection E.fppfSite S E.fppf_mem h f U).symm

/-- At the final objects the projection of
`AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctorTransition`
is `h` itself, as a morphism `Over.mk (h ≫ f) ⟶ Over.mk f` of the slice over `X`. -/
theorem inclusionFunctorTransition_idObj {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X) :
    (inclusionFunctor E (h ≫ f)).map
        ((Space.isTerminal_spacesBaseChange_idObj E.fppfSite S E.fppf_mem h).from
          (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Z)) ≫
      (inclusionFunctorTransition E h f).app (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Y) =
    (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f) := by
  apply Over.OverMorphism.ext
  let b := Space.spacesBaseChange E.fppfSite S E.fppf_mem h
  let k := (Space.isTerminal_spacesBaseChange_idObj E.fppfSite S E.fppf_mem h).from
    (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Z)
  have hk : k.hom.left ≫ (b.functor.obj (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Y)).1.hom
      = 𝟙 Z :=
    Over.w k.hom
  change k.hom.left ≫ b.projection.app _ ≫
    (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Y).1.hom = h
  rw [(b.isPullback (Space.SpacesEtale.idObj E.fppfSite S E.fppf_mem Y)).w, ← Category.assoc, hk]
  exact Category.id_comp _

/-- `AlgebraicGeometry.BigEtaleSpaceSite.smallPullbackIso` carries the unit of `f⁻¹ ⊣ f_*` to the
unit of `π_X⁻¹ ⊣ π_{X,*}` followed by restriction along the projections. -/
theorem smallPullbackIso_unit {Y : E.Spaces} (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (U : (Space.SpacesEtale E.fppfSite S E.fppf_mem X)ᵒᵖ) :
    (((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafAdjunctionContinuous
        (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).unit.app F).hom.app U ≫
      ((smallPullbackIso E f).hom.app F).hom.app
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.op.obj U) =
    (((E.bigToSmallEtaleMorphism X).adj.unit.app F).hom.app U ≫
      ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
        ((inclusionTransition E f).app U.unop).op) :=
  sheafPullbackIsoOfInitial_unit (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (E.bigEtaleTopology X)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (inclusionFunctor E f) (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X)
    (inclusionTransition E f) (E.bigToSmallEtaleMorphism X).inverseImage
    (E.bigToSmallEtaleMorphism X).adj (inclusionTransitionInitial E f) F U

/-- The comparisons `AlgebraicGeometry.BigEtaleSpaceSite.smallPullbackIso` for `f` and `h ≫ f`
are compatible with restriction along the projections `V ×_Y Z ⟶ V`. -/
theorem smallPullbackIso_comp {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    (smallPullbackIso E f).hom.app F ≫
        sheafPushforwardRestriction (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z) (E.bigEtaleTopology X)
          (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
          (inclusionFunctor E f) (inclusionFunctor E (h ≫ f))
          (inclusionFunctorTransition E h f) ((E.bigToSmallEtaleMorphism X).inverseImage.obj F) =
      sheafPullbackRestriction (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)
          (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
          (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
          (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor
          (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f) F ≫
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.sheafPushforwardContinuous
          (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).map
          ((smallPullbackIso E (h ≫ f)).hom.app F) :=
  sheafPullbackRestriction_comp (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z) (E.bigEtaleTopology X)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor
    (inclusionFunctor E f) (inclusionFunctor E (h ≫ f))
    (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem X)
    (E.bigToSmallEtaleMorphism X).inverseImage (E.bigToSmallEtaleMorphism X).adj.unit
    (inclusionTransition E f) (inclusionTransition E (h ≫ f))
    (smallPullbackIso E f).hom (smallPullbackIso E (h ≫ f)).hom
    (smallPullbackIso_unit E f) (smallPullbackIso_unit E (h ≫ f))
    (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f)
    (inclusionFunctorTransition E h f) (inclusionFunctorTransition_comp E h f) F

/-- **The section rule of Stacks 0DG7 is natural.** Restriction of sections of `π_X⁻¹F` along
`Over.mk (h ≫ f) ⟶ Over.mk f` is the canonical map
`AlgebraicGeometry.BigEtaleSpaceSite.sectionsRestriction` of global sections. -/
theorem sectionsIso_restriction {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    (sectionsIso E f).hom.app F ≫ sectionsRestriction E h f F =
      ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
          (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f).op ≫
        (sectionsIso E (h ≫ f)).hom.app F :=
  sheafPullbackSectionsIso_restriction (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z) (E.bigEtaleTopology X)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor
    (inclusionFunctor E f) (inclusionFunctor E (h ≫ f))
    (E.bigToSmallEtaleMorphism X).inverseImage
    (smallPullbackIso E f) (smallPullbackIso E (h ≫ f))
    (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f)
    (inclusionFunctorTransition E h f)
    (Space.SpacesEtale.isTerminal_idObj E.fppfSite S E.fppf_mem Y)
    (Space.isTerminal_spacesBaseChange_idObj E.fppfSite S E.fppf_mem h)
    (Space.SpacesEtale.isTerminal_idObj E.fppfSite S E.fppf_mem Z)
    (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f)
    (inclusionFunctorTransition_idObj E h f) F (smallPullbackIso_comp E h f F)

/-- The section comparison at a single sheaf. -/
def sectionsIsoApp {Y : E.Spaces} (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.obj (op (Over.mk f)) ≅
      (Sheaf.Γ (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (Type (u + 1))).obj
        (((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F) :=
  (sectionsIso E f).app F

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the sheaf pullback and sections of the spaces étale sites is deep
/-- Pointwise form of `AlgebraicGeometry.BigEtaleSpaceSite.sectionsIso_restriction`. -/
theorem map_sectionsIsoApp_inv {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (x : (Sheaf.Γ (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (Type (u + 1))).obj
      (((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F)) :
    ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
        (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f).op ((sectionsIsoApp E f F).inv x) =
      (sectionsIsoApp E (h ≫ f) F).inv (sectionsRestriction E h f F x) := by
  have key : (sectionsIsoApp E f F).inv ≫ ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
        (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f).op =
      sectionsRestriction E h f F ≫ (sectionsIsoApp E (h ≫ f) F).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (sectionsIso_restriction E h f F).symm
  rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]

/-- The inverse image of a terminal small étale sheaf is terminal. -/
def isTerminal_pullback_terminal {Y : E.Spaces} (f : Y ⟶ X) :
    IsTerminal (((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj
        (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))) :=
  letI := (Space.spacesBaseChange_isMorphismOfSites E.fppfSite S E.fppf_mem f).preservesFiniteLimits
  terminalIsTerminal.isTerminalObj _ _

/-- The inverse image of a terminal small étale sheaf, identified with the terminal sheaf. -/
def pullbackTerminalIso {Y : E.Spaces} (f : Y ⟶ X) :
    (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y) (Type (u + 1))) ≅
      ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj
        (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :=
  terminalIsTerminal.uniqueUpToIso (isTerminal_pullback_terminal E f)

/-- Morphisms `f⁻¹⊤ ⟶ f⁻¹F` are the sections of `π_X⁻¹F` over `f`. -/
def homEquivSections {Y : E.Spaces} (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    (((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj
        (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) ⟶
      ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F) ≃
    ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.obj (op (Over.mk f)) :=
  (Iso.homFromEquiv (pullbackTerminalIso E f).symm).trans
    ((Sheaf.ΓEquivHomTerminal _ _).symm.trans (sectionsIsoApp E f F).symm.toEquiv)

/-- The defining formula of `AlgebraicGeometry.BigEtaleSpaceSite.homEquivSections`. -/
theorem homEquivSections_apply {Y : E.Spaces} (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (φ : ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj
        (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) ⟶
      ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F) :
    homEquivSections E f F φ = (sectionsIsoApp E f F).inv
      ((Sheaf.ΓEquivHomTerminal _ _).symm ((pullbackTerminalIso E f).hom ≫ φ)) :=
  rfl

/-- The comparison `f⁻¹ ⋙ h⁻¹ ≅ (h ≫ f)⁻¹` of iterated spaces-étale inverse images: the mate of the
composition isomorphism of base changes. -/
abbrev pullbackCompIso {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X) :=
  Adjunction.leftAdjointCompIso
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafAdjunctionContinuous
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y))
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.sheafAdjunctionContinuous
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z))
    ((Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor.sheafAdjunctionContinuous
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z))
    (Functor.sheafPushforwardContinuousComp' (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h
        f)
      (Type (u + 1)) (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z))

/-- **Naturality of `AlgebraicGeometry.BigEtaleSpaceSite.homEquivSections`**: restriction of
sections of `π_X⁻¹F` along `Over.mk (h ≫ f) ⟶ Over.mk f` is inverse image along `h` followed by
the comparison `h⁻¹f⁻¹ ≅ (h ≫ f)⁻¹`. -/
theorem homEquivSections_naturality {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (φ : ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj
        (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) ⟶
      ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F) :
    homEquivSections E (h ≫ f) F ((pullbackCompIso E h f).inv.app _ ≫
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).map φ ≫
        (pullbackCompIso E h f).hom.app F) =
      ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
        (Over.homMk h rfl : Over.mk (h ≫ f) ⟶ Over.mk f).op (homEquivSections E f F φ) := by
  rw [homEquivSections_apply, homEquivSections_apply, map_sectionsIsoApp_inv]
  congr 1
  refine Eq.trans ?_ (sheafPullbackSectionsRestriction_ΓEquivHomTerminal_symm
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor
    (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor
    (Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f) F
    (Space.SpacesEtale.isTerminal_idObj E.fppfSite S E.fppf_mem Y)
    (Space.isTerminal_spacesBaseChange_idObj E.fppfSite S E.fppf_mem h)
    (isTerminal_pullback_terminal E h)
    ((pullbackTerminalIso E f).hom ≫ φ)
    ((pullbackTerminalIso E (h ≫ f)).hom ≫ (pullbackCompIso E h f).inv.app _ ≫
      ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).map
        (pullbackTerminalIso E f).inv)).symm
  congr 1
  simp

/-- `AlgebraicGeometry.BigEtaleSpaceSite.homEquivSections_naturality` along an arbitrary morphism
`Over.mk c ⟶ Over.mk f` of the slice, with `h ≫ f = c` written as a transport; the comparison on
the terminal sheaf is arbitrary, its target being terminal. -/
theorem homEquivSections_naturality_of_eq {Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X) (c : Z ⟶ X)
    (w : h ≫ f = c)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (φ : ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj (⊤_ Sheaf
              (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) ⟶
              ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.sheafPullback (Type (u +
              1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)).obj F)
    (E₁ : ((Space.spacesBaseChange E.fppfSite S E.fppf_mem c).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).obj (⊤_ Sheaf
              (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) ⟶
              ((Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor.sheafPullback (Type
              (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).obj (⊤_ Sheaf
              (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))))
    (E₂ : ((Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).functor.sheafPullback (Type (u
        + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).obj F ⟶ ((Space.spacesBaseChange
              E.fppfSite S E.fppf_mem c).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).obj F)
    (hE₂ : E₂ = eqToHom (by rw [w])) :
    homEquivSections E c F (E₁ ≫ (pullbackCompIso E h f).inv.app _ ≫
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.sheafPullback (Type (u + 1))
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Y)
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Z)).map φ ≫ (pullbackCompIso E h
              f).hom.app F ≫ E₂) =
      ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj.map
        (Over.homMk h w : Over.mk c ⟶ Over.mk f).op (homEquivSections E f F φ) := by
  subst w hE₂
  obtain rfl : E₁ = 𝟙 _ := (isTerminal_pullback_terminal E (h ≫ f)).hom_ext _ _
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    homEquivSections_naturality E h f F φ

/-- The pseudofunctor of spaces-étale inverse images sends an equality of morphisms to the
corresponding transport. -/
theorem spacesEtalePseudofunctor_map₂_eqToHom
    {A B : LocallyDiscrete (E.Spaces)ᵒᵖ} {f f' : A ⟶ B} (h : f = f')
    (M : (Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).obj A) :
    ((Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).map₂ (eqToHom h)).toNatTrans.app M =
      eqToHom (by rw [h]) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl]
  exact congrArg (fun t => t.toNatTrans.app M)
    ((Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).map₂_id f)

/-- **The presheaf of morphisms from the terminal sheaf to `F` is `π_X⁻¹F`.** For the pseudofunctor
of spaces-étale inverse images, the presheaf `T ↦ (T⁻¹⊤ ⟶ T⁻¹F)` on the slice over `X`
(`CategoryTheory.Pseudofunctor.presheafHom`) is isomorphic to the presheaf underlying `π_X⁻¹F`. -/
def presheafHomIso
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    (Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).presheafHom (⊤_ Sheaf
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) F ≅
      ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj :=
  NatIso.ofComponents (fun T => (homEquivSections E T.unop.hom F).toIso) (by
    rintro ⟨T₁⟩ ⟨T₂⟩ ⟨g⟩
    ext φ
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
    refine Eq.trans (congrArg (homEquivSections E T₂.hom F) ?_)
      (homEquivSections_naturality_of_eq E g.left T₁.hom T₂.hom (Over.w g) F φ
        (((Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).map₂ (eqToHom
          (congrArg (fun x => x.op.toLoc) (Over.w g).symm :
            T₂.hom.op.toLoc = T₁.hom.op.toLoc ≫ g.left.op.toLoc))).toNatTrans.app _)
        (((Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).map₂ (eqToHom
          (congrArg (fun x => x.op.toLoc) (Over.w g) :
            T₁.hom.op.toLoc ≫ g.left.op.toLoc = T₂.hom.op.toLoc))).toNatTrans.app F)
        (spacesEtalePseudofunctor_map₂_eqToHom E _ _))
    dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Pseudofunctor.mapComp']
    rfl)

/-- **Descent along one arrow from full faithfulness of descent.** If the pseudofunctor of
spaces-étale inverse images is a prestack for the sieve generated by `f.left`, then `π_X⁻¹F`
satisfies the sheaf condition for the single arrow `f : V ⟶ U` of the slice over `X`. -/
theorem isSheafFor_inverseImage_singleton_of_isPrestackFor {U V : Over X} (f : V ⟶ U)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    (hf : (Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).IsPrestackFor
      (Sieve.ofArrows (fun _ : Unit ↦ V.left) (fun _ ↦ f.left)).arrows) :
    Presieve.IsSheafFor ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj
      (Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f)) := by
  have h1 := ((Space.spacesEtalePseudofunctor E.fppfSite S E.fppf_mem).isPrestackFor_iff_isSheafFor'
    _).mp hf (⊤_ Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1)))
    F U.hom
  rw [Presieve.isSheafFor_iff_of_iso (presheafHomIso E F)] at h1
  have hs : (Sieve.overEquiv U).symm (Sieve.ofArrows (fun _ : Unit ↦ V.left) (fun _ ↦ f.left)) =
      Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f) := by
    apply (Sieve.overEquiv U).injective
    rw [OrderIso.apply_symm_apply, Sieve.overEquiv_ofArrows]
  rw [Presieve.isSheafFor_iff_generate]
  change Presieve.IsSheafFor _ (Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f)).arrows
  rwa [← hs]

/-- **Proper surjective descent for `π_X⁻¹F`**, granted the scheme case of full faithfulness of
descent along proper surjections: `π_X⁻¹F` satisfies the sheaf condition for every morphism of
the slice over `X` whose underlying morphism of algebraic spaces is proper and surjective. -/
theorem isSheafFor_inverseImage_of_isProper_isSurjective
    (H : Space.ProperSurjectivePrestackOverSchemes E.fppfSite S E.fppf_mem)
    {U V : Over X} (f : V ⟶ U)
    (hp : Space.IsProper E.fppfSite S E.fppf_mem f.left.hom)
    (hs : Space.IsSurjective E.fppfSite S E.fppf_mem f.left.hom)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X) (Type (u + 1))) :
    Presieve.IsSheafFor ((E.bigToSmallEtaleMorphism X).inverseImage.obj F).obj
      (Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f)) :=
  isSheafFor_inverseImage_singleton_of_isPrestackFor E f F
    (Space.isPrestackFor_of_isProper_isSurjective H f.left hp hs)

end AlgebraicGeometry.BigEtaleSpaceSite

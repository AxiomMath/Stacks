module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackGerm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleExchange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverDescent
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of modules along a flat morphism is exact on the spaces-étale sites

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S`. The pullback `f^*`
of modules along the morphism of spaces-étale ringed topoi of `f` (Stacks 0DE7), with sections in
the universe of the spaces-étale site, preserves finite limits.

The proof is stalkwise at the universe-lifted geometric points of `X`, which form a conservative
family of points of the spaces-étale site (every point of an algebraic space is the image of a
geometric point). At such a point `x` the stalk of `f^*G` is the stalk of `G` at `f ∘ x` with
scalars extended along a homomorphism of structure-sheaf stalks (Stacks 05V5). The stalk of the
spaces-étale structure sheaf at `x` is the étale local ring (Stacks 04KG), the small étale
neighbourhoods being initial among the étale neighbourhoods, and on germs that homomorphism
pulls regular functions back along every commuting diagram of pointed étale charts; so it is
the homomorphism of étale local rings of Stacks 04NG, which that lemma shows is flat for flat `f`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `isConservativeFamilyOfPoints_sitePoint_spacesEtaleModulePullbackFlatExact`: the
  universe-lifted geometric points form a conservative family of points of the spaces-étale site.
* `spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact`: the stalk of the structure sheaf
  at a geometric point is the étale local ring.
* `isEtaleLocalRingMap_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact` and
  `flat_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact`: the homomorphism of
  stalks is the map of étale local rings, hence flat for flat `f`.
* **Pullback along a flat morphism is exact on the spaces-étale sites**:
preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- An exact sequence stays exact under `F` followed by `G` when the composite is exact. -/
private theorem exact_map_map_of_comp (hF : F.PreservesZeroMorphisms)
    (hG : G.PreservesZeroMorphisms) (hl : PreservesFiniteLimits (F ⋙ G))
    (hc : PreservesFiniteColimits (F ⋙ G)) {σ : ShortComplex C} (hσ : σ.Exact) :
    ((σ.map F).map G).Exact :=
  hσ.map (F ⋙ G)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The image under `G` of `0 ⟶ F A ⟶ F B` is exact when `F ⋙ G` carries the monomorphism
`A ⟶ B` to a monomorphism. -/
private theorem exact_map_mk_zero_of_mono (_hF : F.PreservesZeroMorphisms)
    (hG : G.PreservesZeroMorphisms) (hl : PreservesFiniteLimits (F ⋙ G)) {A B : C}
    (f : A ⟶ B) [Mono f] :
    ((ShortComplex.mk (0 : F.obj A ⟶ F.obj A) (F.map f) zero_comp).map G).Exact :=
  (ShortComplex.exact_iff_mono _ (G.map_zero _ _)).2
    (inferInstanceAs (Mono ((F ⋙ G).map f)))

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Space

open SimplicialSpacesEtaleSite ExtensionByZeroStalk

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- Base change of algebraic spaces étale over `Y` along `f`, followed by the fibre functor of the
universe-lifted point at `x`, is the fibre functor of the universe-lifted point at `f ∘ x`
(Stacks 03G2, read on lifts of geometric points). -/
def spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact :
    (spacesBaseChange B S hS f).functor ⋙ (sitePoint x).fiber ≅
      (sitePoint (geometricPointMap f.hom x)).fiber :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesBaseChangeFiberIso B S hS f x) uliftFunctor.{u + 1}

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The direct image along the spaces-étale morphism of `f` of the skyscraper at `x` is the
skyscraper at `f ∘ x`, by reindexing the products along the fibre comparison. -/
def spacesEtaleSkyscraperIsoSpacesEtaleModulePullbackFlatExact :
    (sitePoint x).skyscraperSheafFunctor (A := Type (u + 1)) ⋙
        (spacesEtaleRingedToposHom f).toToposHom.pushforward ≅
      (sitePoint (geometricPointMap f.hom x)).skyscraperSheafFunctor :=
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  Point.skyscraperPushforwardIso (sitePoint x) (sitePoint (geometricPointMap f.hom x))
    (spacesBaseChange B S hS f).functor
    (spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **Stacks 04K2, part (4), on the spaces-étale sites at the universe of the modules.** The
fibre at `x` of the inverse image of a sheaf of sets is its fibre at `f ∘ x`; it is the
right-adjoint transpose of `spacesEtaleSkyscraperIsoSpacesEtaleModulePullbackFlatExact`. -/
@[sga "4½ Arcata 2.3.3" "more general"]
def spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact :
    (sitePoint (geometricPointMap f.hom x)).sheafFiber (A := Type (u + 1)) ≅
      (spacesEtaleRingedToposHom f).toToposHom.inverseImage ⋙
        (sitePoint x).sheafFiber (A := Type (u + 1)) :=
  (conjugateIsoEquiv
      ((spacesEtaleRingedToposHom f).toToposHom.adj.comp
        (sitePoint x).skyscraperSheafAdjunction)
      (sitePoint (geometricPointMap f.hom x)).skyscraperSheafAdjunction).symm
    (spacesEtaleSkyscraperIsoSpacesEtaleModulePullbackFlatExact f x)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The homomorphism `(𝒪_Y)_{f ∘ x} ⟶ (𝒪_X)_x` of structure-sheaf stalks along which the stalk of
a pullback of modules extends scalars (Stacks 05V5), for the spaces-étale ringed topoi. -/
abbrev spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact :=
  Stacks.Sheaves.StalkPullback.stalkRingMap (spacesEtaleRingedToposHom f).toModulesHom
    (sitePoint x) (sitePoint (geometricPointMap f.hom x))
    (spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact f x)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The sheaf of sets underlying the structure sheaf of the spaces-étale ringed topos. -/
abbrev spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact
    (Z : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1)) :=
  (sheafCompose (SpacesEtale.topology B S hS Z) (forget RingCat.{u + 1})).obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS Z).O)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The fibre at `x` of the sheaf of sets underlying the structure sheaf of `X`. -/
abbrev spacesEtaleStructureSetFiberSpacesEtaleModulePullbackFlatExact :=
  ((sitePoint x).sheafFiber (A := Type (u + 1))).obj
    (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- Germ formation at `x`, as a map into the skyscraper with value the fibre. -/
abbrev spacesEtaleStructureSetUnitSpacesEtaleModulePullbackFlatExact :
    spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X ⟶
      (sitePoint x).skyscraperSheafFunctor.obj
        (spacesEtaleStructureSetFiberSpacesEtaleModulePullbackFlatExact x) :=
  ((sitePoint x).skyscraperSheafAdjunction (A := Type (u + 1))).homEquiv
    (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X)
    (spacesEtaleStructureSetFiberSpacesEtaleModulePullbackFlatExact x) (𝟙 _)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **The germ formula on sheaves of sets**: the fibre comparison followed by the fibre of the
inverse-image structure map carries the germ of a section over `V` at a lift of `f ∘ x` to the
germ of its image under the structure map at the corresponding lift of `x` into `V ×_Y X`. -/
theorem spacesEtaleStructureSetFiberMap_germ_spacesEtaleModulePullbackFlatExact
    (V : SpacesEtale B S hS Y)
    (v : (sitePoint (geometricPointMap f.hom x)).fiber.obj V)
    (s : (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y).obj.obj (op V)) :
    ((sitePoint x).sheafFiber (A := Type (u + 1))).map
        ((sheafCompose (SpacesEtale.topology B S hS X) (forget RingCat.{u + 1})).map
          (spacesEtaleRingedToposHom f).toModulesHom.fSharpInverseImage)
      ((spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact f x).hom.app
          (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y)
        ((sitePoint (geometricPointMap f.hom x)).toPresheafFiber V v
          (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y).obj s)) =
      (sitePoint x).toPresheafFiber ((spacesBaseChange B S hS f).functor.obj V)
        ((spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app V v)
        (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X).obj
        (((sheafCompose (SpacesEtale.topology B S hS Y) (forget RingCat.{u + 1})).map
          (spacesEtaleRingedToposHom f).toModulesHom.fSharp).hom.app (op V) s) := by
  let := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hadj : ((spacesEtaleRingedToposHom f).toModulesHom.toToposHom.adj.homEquiv
        (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y)
        (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X)).symm
      ((sheafCompose (SpacesEtale.topology B S hS Y) (forget RingCat.{u + 1})).map
        (spacesEtaleRingedToposHom f).toModulesHom.fSharp) =
      (sheafCompose (SpacesEtale.topology B S hS X) (forget RingCat.{u + 1})).map
        (spacesEtaleRingedToposHom f).toModulesHom.fSharpInverseImage :=
    (Equiv.symm_apply_eq _).2 (spacesEtaleRingedToposHom f).toModulesHom.fSharp_adjunct
  have hcc := Adjunction.conjugate_comp
    (A := spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y)
    (B := spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X)
    (M := spacesEtaleStructureSetFiberSpacesEtaleModulePullbackFlatExact x)
    (spacesEtaleRingedToposHom f).toModulesHom.toToposHom.adj
    ((sitePoint x).skyscraperSheafAdjunction (A := Type (u + 1)))
    ((sitePoint (geometricPointMap f.hom x)).skyscraperSheafAdjunction (A := Type (u + 1)))
    (spacesEtaleSkyscraperIsoSpacesEtaleModulePullbackFlatExact f x)
    ((sheafCompose (SpacesEtale.topology B S hS Y) (forget RingCat.{u + 1})).map
      (spacesEtaleRingedToposHom f).toModulesHom.fSharp)
    (𝟙 _) _ (Equiv.apply_symm_apply _ _).symm
  rw [hadj, Category.comp_id] at hcc
  have hgerm := congrArg (fun k => (sitePoint (geometricPointMap f.hom x)).toPresheafFiber V v
    (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact Y).obj ≫ k) hcc
  simp only at hgerm
  rw [Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm] at hgerm
  refine Eq.trans (types_congr_hom hgerm s) ?_
  refine Eq.trans (types_congr_hom (Point.skyscraperPushforwardIso_hom_app_π (sitePoint x)
    (sitePoint (geometricPointMap f.hom x)) (spacesBaseChange B S hS f).functor
    (spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x)
    (spacesEtaleStructureSetFiberSpacesEtaleModulePullbackFlatExact x) V v)
    (((spacesEtaleRingedToposHom f).toModulesHom.toToposHom.pushforward.map
        (spacesEtaleStructureSetUnitSpacesEtaleModulePullbackFlatExact x)).hom.app (op V)
      (((sheafCompose (SpacesEtale.topology B S hS Y) (forget RingCat.{u + 1})).map
        (spacesEtaleRingedToposHom f).toModulesHom.fSharp).hom.app (op V) s))) ?_
  exact types_congr_hom (Point.skyscraperSheafAdjunction_unit_π (sitePoint x)
    (spacesEtaleStructureSetSheafSpacesEtaleModulePullbackFlatExact X)
    ((spacesBaseChange B S hS f).functor.obj V)
    ((spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app V v)) _

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The small étale neighbourhoods of `x`, read as elements of the fibre functor of the
universe-lifted spaces-étale point. -/
def neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact :
    SmallEtaleNeighborhood x ⥤ (sitePoint x).fiber.Elements :=
  (neighborhoodFiberElementsEquiv B S hS X.1 x).functor ⋙
    smallToSpacesFiberElements B S hS x ⋙
      Functor.Elements.ulift.{u + 1} (spacesGeometricFiber x)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The small étale neighbourhoods are initial among the lifts of `x` into the spaces-étale
site. -/
instance initial_neighborhoodToSpacesPointElements_spacesEtaleModulePullbackFlatExact :
    (neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).Initial := by
  have : (Functor.Elements.ulift.{u + 1} (spacesGeometricFiber x)).Initial :=
    inferInstanceAs (Functor.Elements.uliftEquiv.{u + 1} (spacesGeometricFiber x)).functor.Initial
  exact inferInstanceAs (Functor.Initial ((neighborhoodFiberElementsEquiv B S hS X.1 x).functor ⋙
    smallToSpacesFiberElements B S hS x ⋙
      Functor.Elements.ulift.{u + 1} (spacesGeometricFiber x)))

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- A small étale neighbourhood is sent to the image of its chart, with the lifted point. -/
theorem neighborhoodToSpacesPointElements_obj_spacesEtaleModulePullbackFlatExact
    (U : SmallEtaleNeighborhood x) :
    (neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).obj U =
      (sitePoint x).fiber.elementsMk ((comparisonFunctor B S hS X).obj U.chart)
        (ULift.up ⟨U.point, U.point_comp⟩) := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The structure sheaf of the spaces-étale site along the small étale neighbourhoods is the
universe lift of the structure sheaf of the small étale site. -/
def neighborhoodStructureIsoSpacesEtaleModulePullbackFlatExact :
    (neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op ⋙
        (Functor.Elements.π (sitePoint x).fiber).op ⋙
          (SpacesEtale.structureSheaf B S hS X).obj ≅
      SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS X.1) :=
  NatIso.ofComponents
    (fun U =>
      globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.unop.chart))
    (by
      intro U V g
      exact globalFunctionsSchemeSpaceIso_naturality B S hS
        ((SmallEtale.toOver B S hS X.1).map g.unop.hom))

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The structure sheaf along the small étale neighbourhoods has a colimit. -/
instance
    hasColimit_neighborhoodToSpacesPointElements_structureSheaf_spacesEtaleModulePullbackFlatExact :
    HasColimit ((neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op ⋙
    (Functor.Elements.π (sitePoint x).fiber).op ⋙ (SpacesEtale.structureSheaf B S hS X).obj) :=
  Functor.Final.comp_hasColimit _

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **The stalk of the spaces-étale structure sheaf at a geometric point is the étale local
ring** (Stacks 04KG). -/
def spacesPointStalkRingIsoSpacesEtaleModulePullbackFlatExact :
    Stacks.ringFiber (sitePoint x) (SpacesEtale.structureSheaf B S hS X).obj ≅
      etaleLocalRing B S hS X.1 x :=
  (Functor.Final.colimitIso
      (neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op
      ((Functor.Elements.π (sitePoint x).fiber).op ⋙
        (SpacesEtale.structureSheaf B S hS X).obj)).symm ≪≫
    HasColimit.isoOfNatIso (neighborhoodStructureIsoSpacesEtaleModulePullbackFlatExact x)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The comparison with the étale local ring sends the germ of a transported regular function on
a small étale neighbourhood to its germ in the étale local ring. -/
theorem spacesPointStalkRingIso_germ_spacesEtaleModulePullbackFlatExact
    (U : SmallEtaleNeighborhood x) (a : (structurePresheaf B S hS X.1).obj (op U.chart)) :
    (spacesPointStalkRingIsoSpacesEtaleModulePullbackFlatExact x).hom.hom
        ((sitePoint x).toPresheafFiber
          ((comparisonFunctor B S hS X).obj U.chart) (ULift.up ⟨U.point, U.point_comp⟩)
          (SpacesEtale.structureSheaf B S hS X).obj
          ((globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.chart)).inv
            (ULift.up a))) =
      etaleLocalRingGerm B S hS X.1 x (op U) a := by
  have h1 := Functor.Final.ι_colimitIso_inv
    (neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op
    ((Functor.Elements.π (sitePoint x).fiber).op ⋙ (SpacesEtale.structureSheaf B S hS X).obj)
    (op U)
  have h2 := HasColimit.ι_isoOfNatIso_hom
    (neighborhoodStructureIsoSpacesEtaleModulePullbackFlatExact x) (op U)
  have key : colimit.ι ((Functor.Elements.π (sitePoint x).fiber).op ⋙
        (SpacesEtale.structureSheaf B S hS X).obj)
        ((neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op.obj (op U)) ≫
          (spacesPointStalkRingIsoSpacesEtaleModulePullbackFlatExact x).hom =
      (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.chart)).hom ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS X.1))
          (op U) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans h2)
  have key2 :
      (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.chart)).inv ≫
      colimit.ι ((Functor.Elements.π (sitePoint x).fiber).op ⋙
        (SpacesEtale.structureSheaf B S hS X).obj)
        ((neighborhoodToSpacesPointElementsSpacesEtaleModulePullbackFlatExact x).op.obj (op U)) ≫
          (spacesPointStalkRingIsoSpacesEtaleModulePullbackFlatExact x).hom =
      colimit.ι (SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS X.1))
        (op U) :=
    (congrArg (fun k => (globalFunctionsSchemeSpaceIso B S hS
      ((SmallEtale.toOver B S hS X.1).obj U.chart)).inv ≫ k) key).trans
      (Iso.inv_hom_id_assoc _ _)
  exact ConcreteCategory.congr_hom key2 (ULift.up a)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
open Stacks.Sheaves.StalkPullback Stacks.Sheaves.StalkTransport in
/-- **The homomorphism of structure-sheaf stalks on germs**: the germ at a lift of `f ∘ x̄`
of a section over `V` goes to the germ, at the corresponding lift of `x̄` into `V ×_Y X`, of its
pullback along the projection. -/
theorem spacesEtaleStalkPullbackRingMap_germ_spacesEtaleModulePullbackFlatExact
    (V : SpacesEtale B S hS Y)
    (v : (sitePoint (geometricPointMap f.hom x)).fiber.obj V)
    (s : (SpacesEtale.structureSheaf B S hS Y).obj.obj (op V)) :
    spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x
        ((sitePoint (geometricPointMap f.hom x)).toPresheafFiber V v
          (SpacesEtale.structureSheaf B S hS Y).obj s) =
      (sitePoint x).toPresheafFiber ((spacesBaseChange B S hS f).functor.obj V)
        ((spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app V v)
        (SpacesEtale.structureSheaf B S hS X).obj
        ((globalFunctionsPresheaf B S hS).map
          ((spacesBaseChange B S hS f).projection.app V).op s) := by
  refine Eq.trans (stalkRingMap_toPresheafFiber (spacesEtaleRingedToposHom f).toModulesHom
    (sitePoint x) (sitePoint (geometricPointMap f.hom x))
    (spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact f x) V v s) ?_
  refine Eq.trans (congrArg (fun z => (Stacks.commRingPresheafFiberIso
      (sitePoint x) (SpacesEtale.structureSheaf B S hS X).obj).hom.hom
    (ringStalkComparison (sitePoint x)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O) z))
    (spacesEtaleStructureSetFiberMap_germ_spacesEtaleModulePullbackFlatExact f x V v s)) ?_
  refine Eq.trans (congrArg (Stacks.commRingPresheafFiberIso
    (sitePoint x) (SpacesEtale.structureSheaf B S hS X).obj).hom.hom
    (ringStalkComparison_ringGerm (sitePoint x)
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)
      ((spacesBaseChange B S hS f).functor.obj V)
      ((spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app V v)
      ((globalFunctionsPresheaf B S hS).map
          ((spacesBaseChange B S hS f).projection.app V).op s))) ?_
  exact Stacks.commRingPresheafFiberIso_hom_toPresheafFiber
    (sitePoint x) (SpacesEtale.structureSheaf B S hS X).obj
    ((spacesBaseChange B S hS f).functor.obj V)
    ((spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app V v)
    ((globalFunctionsPresheaf B S hS).map ((spacesBaseChange B S hS f).projection.app V).op s)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- The stalk of the spaces-étale structure sheaf at a geometric point is the étale local
ring, as an isomorphism of rings. -/
def spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact :
    Stacks.ringFiber (sitePoint x) (SpacesEtale.structureSheaf B S hS X).obj ≃+*
      etaleLocalRing B S hS X.1 x :=
  (spacesPointStalkRingIsoSpacesEtaleModulePullbackFlatExact x).commRingCatIsoToRingEquiv

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- Applying the universe lift of a ring homomorphism, as a morphism of `CommRingCat`, to a
lifted element. -/
private theorem ofHom_ulift_apply {R R' : Type u} [CommRing R] [CommRing R'] (r : R →+* R')
    (a : R) :
    (CommRingCat.ofHom (r.ulift.{u + 1, u + 1, u, u})).hom (ULift.up a) = ULift.up (r a) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- Pulling back a regular function along a morphism of étale charts, read in the spaces-étale
structure sheaf through the comparison of Stacks 03G1: a morphism between the images of two
charts whose underlying morphism of presheaves is a Yoneda morphism pulls the transported
function back to the transported pullback. -/
theorem globalFunctionsSchemeSpaceIso_inv_apply_comparison_spacesEtaleModulePullbackFlatExact
    {X' Y' : AlgebraicSpaces B S hS} {U : SmallEtale B S hS X'.1} {V : SmallEtale B S hS Y'.1}
    (g : U.obj.left ⟶ V.obj.left)
    (k : (SpacesEtale.toSpaces B S hS X').obj ((comparisonFunctor B S hS X').obj U) ⟶
      (SpacesEtale.toSpaces B S hS Y').obj ((comparisonFunctor B S hS Y').obj V))
    (hk : k.hom = yoneda.map g) (s : (structurePresheaf B S hS Y'.1).obj (op V)) :
    (globalFunctionsPresheaf B S hS).map k.op
        ((globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS Y'.1).obj V)).inv
          (ULift.up s)) =
      (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X'.1).obj U)).inv
        (ULift.up (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op s)) := by
  obtain rfl : k = (schemeSpaceFunctor B S hS).map g := ObjectProperty.hom_ext _ hk
  have hm2 : (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS Y'.1).obj V)).inv ≫
      (globalFunctionsPresheaf B S hS).map ((schemeSpaceFunctor B S hS).map g).op =
      CommRingCat.ofHom ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom.ulift) ≫
        (globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X'.1).obj U)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, globalFunctionsSchemeSpaceIso_naturality B S hS
      (V := (SmallEtale.toOver B S hS X'.1).obj U) (W := (SmallEtale.toOver B S hS Y'.1).obj V) g,
      Iso.inv_hom_id_assoc]
  have h := ConcreteCategory.congr_hom hm2 (ULift.up s)
  exact h.trans (congrArg (globalFunctionsSchemeSpaceIso B S hS
    ((SmallEtale.toOver B S hS X'.1).obj U)).inv.hom (ofHom_ulift_apply _ s))

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **The germ characterization**: transported to the étale local rings, the homomorphism of
structure-sheaf stalks pulls germs back in every commuting diagram of pointed étale charts. -/
theorem isEtaleLocalRingMap_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact :
    IsEtaleLocalRingMap f.hom x
      (((spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x).toRingHom.comp
          (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x)).comp
        (spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact
          (geometricPointMap f.hom x)).symm.toRingHom) := by
  intro U V g hcomm hpoint
  refine RingHom.ext fun s => ?_
  let d : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨U.chart, V.chart, g, hcomm⟩
  let θU := globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS X.1).obj U.chart)
  let θV := globalFunctionsSchemeSpaceIso B S hS ((SmallEtale.toOver B S hS Y.1).obj V.chart)
  let p : GeometricFiber B S hS X.1 x U.chart := ⟨U.point, U.point_comp⟩
  let q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) V.chart := ⟨V.point, V.point_comp⟩
  have e2 :=
    globalFunctionsSchemeSpaceIso_inv_apply_comparison_spacesEtaleModulePullbackFlatExact g
    ((SpacesEtale.toSpaces B S hS X).map (baseChangeArrowOfChartDiagram B S hS f d) ≫
      (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V.chart))
    (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d) s
  have e1m : (globalFunctionsPresheaf B S hS).map
      ((SpacesEtale.toSpaces B S hS X).map (baseChangeArrowOfChartDiagram B S hS f d) ≫
        (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V.chart)).op =
      (globalFunctionsPresheaf B S hS).map ((spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj V.chart)).op ≫
        (SpacesEtale.structureSheaf B S hS X).obj.map
          (baseChangeArrowOfChartDiagram B S hS f d).op := by
    rw [op_comp, Functor.map_comp]
    rfl
  have e1 := ConcreteCategory.congr_hom e1m (θV.inv (ULift.up s))
  have hY :=
    spacesPointStalkRingIso_germ_spacesEtaleModulePullbackFlatExact (geometricPointMap f.hom x) V s
  have hX := spacesPointStalkRingIso_germ_spacesEtaleModulePullbackFlatExact x U
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op s)
  have hg := spacesEtaleStalkPullbackRingMap_germ_spacesEtaleModulePullbackFlatExact f x
    ((comparisonFunctor B S hS Y).obj V.chart) (ULift.up q) (θV.inv (ULift.up s))
  have hfib : (spacesBaseChangeFiberIsoULiftSpacesEtaleModulePullbackFlatExact f x).inv.app
      ((comparisonFunctor B S hS Y).obj V.chart) (ULift.up q) =
        (sitePoint x).fiber.map (baseChangeArrowOfChartDiagram B S hS f d) (ULift.up p) :=
    congrArg ULift.up (spacesBaseChangeFiberIso_inv_app B S hS f x d p q hpoint)
  have hw := ConcreteCategory.congr_hom ((sitePoint x).toPresheafFiber_w
    (baseChangeArrowOfChartDiagram B S hS f d) (ULift.up p)
    (SpacesEtale.structureSheaf B S hS X).obj)
    ((globalFunctionsPresheaf B S hS).map ((spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj V.chart)).op (θV.inv (ULift.up s)))
  have hY' :
      (spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact (geometricPointMap f.hom x)).symm
      (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) s) =
      (sitePoint (geometricPointMap f.hom x)).toPresheafFiber
        ((comparisonFunctor B S hS Y).obj V.chart) (ULift.up q)
        (SpacesEtale.structureSheaf B S hS Y).obj (θV.inv (ULift.up s)) :=
    (RingEquiv.symm_apply_eq _).2 hY.symm
  refine hX.symm.trans ?_
  change spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x _ =
    spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x
      (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x
        ((spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact
            (geometricPointMap f.hom x)).symm
          (etaleLocalRingGerm B S hS Y.1 (geometricPointMap f.hom x) (op V) s)))
  rw [hY', hg, hfib, ← hw]
  exact congrArg (fun t => spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x
      ((sitePoint x).toPresheafFiber ((comparisonFunctor B S hS X).obj U.chart) (ULift.up p)
        (SpacesEtale.structureSheaf B S hS X).obj t))
    (e2.symm.trans e1)

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **The universe-lifted geometric points are a conservative family of points of the
spaces-étale site.** A sieve through which every lift of every geometric point lifts contains a
jointly point-surjective family, since every point of an algebraic space is the image of a
geometric point. -/
theorem isConservativeFamilyOfPoints_sitePoint_spacesEtaleModulePullbackFlatExact
    (X : AlgebraicSpaces B S hS) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun x : GeometricPoint B S hS X.1 => sitePoint x)) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro V R hR
  let E : PreZeroHypercover.{u + 1} V :=
    { I₀ := Σ W : SpacesEtale B S hS X, {g : W ⟶ V // R g}
      X i := i.1
      f i := i.2.1 }
  have hcov : SpacesEtale.IsCovering B S hS X ⟨V, E⟩ := by
    intro z
    obtain ⟨p, hp⟩ := exists_geometricRepresentative B S hS
      ((SpacesEtale.toSpaces B S hS X).obj V).1 z
    let x := geometricPointMap ((SpacesEtale.inclusion B S hS X).obj V).hom.hom p
    let v : Lifts V x := ⟨p.val.value, rfl⟩
    obtain ⟨W, g, hg, w, hw⟩ := hR ⟨sitePoint x, ObjectProperty.ofObj_apply _ x⟩ (ULift.up v)
    refine ⟨⟨W, g, hg⟩, (liftGeometricPoint w.down).image, ?_⟩
    rw [← hp, ← geometricPointMap_image]
    congr 1
    apply Subtype.ext
    dsimp only [geometricPointMap, liftGeometricPoint, FieldValuedPoint.map]
    congr 1
    exact congrArg (fun t => t.down.1) hw
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck
      ((SpacesEtale.mem_precoverage_iff B S hS X).2 ⟨E, rfl, hcov⟩))
  rintro W g ⟨Z, k, h, ⟨i⟩, rfl⟩
  exact R.downward_closed i.2.2 k

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
/-- **The homomorphism of structure-sheaf stalks of a flat morphism is flat**: transported to
the étale local rings it is the homomorphism of Stacks 04NG, which that lemma shows is flat. -/
theorem flat_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact
    (hf : IsFlat B S hS f.hom) :
    (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x).Flat := by
  have heq := eq_etaleLocalRingMap X.2 f.hom x
    (isEtaleLocalRingMap_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact f x)
  have hcomp := flat_etaleLocalRingMap B S hS X.2 Y.2 f.hom hf x
  rw [← heq] at hcomp
  have hY : (spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact
      (geometricPointMap f.hom x)).toRingHom.Flat :=
    RingHom.Flat.of_bijective (RingEquiv.bijective _)
  have hX : (spacesPointStalkRingEquivSpacesEtaleModulePullbackFlatExact x).symm.toRingHom.Flat :=
    RingHom.Flat.of_bijective (RingEquiv.bijective _)
  convert (hY.comp hcomp).comp hX using 1
  refine RingHom.ext fun z => ?_
  simp

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
set_option maxHeartbeats 1000000 in
-- composing the stalk functor with `ModuleCat.extendScalars` across universe levels is heavy
/-- The pullback of modules along a flat morphism of the spaces-étale morphism, followed by the
stalk at a geometric point of the source, preserves finite limits and finite colimits. -/
private theorem preservesFiniteLimits_and_colimits_spacesEtale_pullbackModules_comp_stalk
    (hf : IsFlat B S hS f.hom) :
    PreservesFiniteLimits ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ⋙
      Stacks.sheafModuleFiberOfCommRing (sitePoint x) (spacesEtaleRingedTopos B S hS X).O) ∧
    PreservesFiniteColimits ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ⋙
      Stacks.sheafModuleFiberOfCommRing (sitePoint x) (spacesEtaleRingedTopos B S hS X).O) := by
  have iso := (Stacks.Sheaves.StalkPullback.stalkFunctorIso
    (spacesEtaleRingedToposHom f).toModulesHom (sitePoint x)
    (sitePoint (geometricPointMap f.hom x))
    (spacesEtaleInverseImageFiberIsoSpacesEtaleModulePullbackFlatExact f x)).symm
  obtain ⟨-, hstalk⟩ := (exactFunctor_iff _).mp
    (Stacks.exactFunctor_sheafModuleFiberOfCommRing
      (sitePoint (geometricPointMap f.hom x)) (spacesEtaleRingedTopos B S hS Y).O)
  have := Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (sitePoint (geometricPointMap f.hom x)) (spacesEtaleRingedTopos B S hS Y).O
  have := ModuleCat.extendScalars_preservesFiniteLimits_of_flat
    (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x)
    (flat_spacesEtaleStalkPullbackRingMap_spacesEtaleModulePullbackFlatExact f x hf)
  have := ModuleCat.extendScalars_preservesFiniteColimits.{u + 1, u + 1, u + 1}
    (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x)
  have hl := comp_preservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing
    (sitePoint (geometricPointMap f.hom x)) (spacesEtaleRingedTopos B S hS Y).O)
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x))
  have hc := comp_preservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing
    (sitePoint (geometricPointMap f.hom x)) (spacesEtaleRingedTopos B S hS Y).O)
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (spacesEtaleStalkPullbackRingMapSpacesEtaleModulePullbackFlatExact f x))
  exact ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _ iso hl,
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _ iso hc⟩

set_option synthInstance.maxHeartbeats 400000 in
-- this was a file-wide setting: instance search in this file is heavy
set_option maxHeartbeats 1000000 in
-- elaborating short complexes of module sheaves on the spaces-étale site is heavy
/-- **Pullback of modules on the spaces-étale sites along a flat morphism is exact.** For a flat
morphism `f : X ⟶ Y` of algebraic spaces, `f^*` from `𝒪_Y`-modules to `𝒪_X`-modules on the
spaces-étale sites preserves finite limits: exactness is checked on the stalks at the geometric
points of `X`, where `f^*` is a flat base change of an exact stalk functor (Stacks 05V5). -/
theorem
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    (hf : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules := by
  have hadd : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
    RingedToposHom.pullbackModules_additive (spacesEtaleRingedToposHom f)
  have hzF : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hz : ∀ x : GeometricPoint B S hS X.1, (Stacks.sheafModuleFiberOfCommRing (sitePoint x)
      (spacesEtaleRingedTopos B S hS X).O).PreservesZeroMorphisms := fun x =>
    Stacks.preservesZeroMorphisms_sheafModuleFiberOfCommRing
      (spacesEtaleRingedTopos B S hS X).O (sitePoint x)
  have key : ∀ τ : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)),
      (∀ x : GeometricPoint B S hS X.1, (@ShortComplex.map _ _ _ _ _ _ τ
        (Stacks.sheafModuleFiberOfCommRing (sitePoint x) (spacesEtaleRingedTopos B S hS X).O)
        (hz x)).Exact) → τ.Exact := fun τ h =>
    (Stacks.shortComplex_exact_iff_forall_exact_map_sheafModuleFiberOfCommRing
      (spacesEtaleRingedTopos B S hS X).O
      (isConservativeFamilyOfPoints_sitePoint_spacesEtaleModulePullbackFlatExact X)).2 (by
        rintro ⟨Φ, hΦ⟩
        obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
        exact h x)
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun σ hσ => ?_
  have hmono := hσ.mono_f
  refine ⟨key _ fun x => ?_, ?_⟩
  · obtain ⟨_, _⟩ :=
      preservesFiniteLimits_and_colimits_spacesEtale_pullbackModules_comp_stalk f x hf
    exact ShortComplex.exact_map_map_of_comp _ _ hzF (hz x) inferInstance inferInstance hσ.exact
  · let T : ShortComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
      ShortComplex.mk (0 : (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj σ.X₁ ⟶
          (spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.obj σ.X₁)
        ((spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.map σ.f) zero_comp
    refine (T.exact_iff_mono rfl).1 (key _ fun x => ?_)
    obtain ⟨_, _⟩ :=
      preservesFiniteLimits_and_colimits_spacesEtale_pullbackModules_comp_stalk f x hf
    exact ShortComplex.exact_map_mk_zero_of_mono _ _ hzF (hz x) inferInstance σ.f


end AlgebraicGeometry.Space

end

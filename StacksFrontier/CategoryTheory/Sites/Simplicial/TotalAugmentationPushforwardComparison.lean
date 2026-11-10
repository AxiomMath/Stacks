module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkLimit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism

/-!
# The two constructions of the direct image of a total augmentation agree

Let `C` be a simplicial family of sites whose transition functors are cocontinuous and let `a` be
an augmentation of `C` towards a site `(D, K)`. There are two constructions of the direct image of
the total augmentation. One is the direct image along the cocontinuous functor out of the total
category assembled from the vertex functors, which is
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi`. The other is the
limit over the simplex category of the cosimplicial sheaf of the direct images of the components,
which is `CategoryTheory.SimplicialSiteSituation.Augmentation.pushforward` read at the
simplicial-site situation of `C`. This file identifies them.

The two are not definitionally equal: the second is a limit, taken through an unexposed choice of
limit cone, and the first is a right Kan extension. What makes them agree is that the first one is
*also* a limit of that same cosimplicial sheaf. Its legs are the maps to the direct images of the
components, and Stacks 0D70 (3) says that the degree-zero leg is a limit fork of the two vertex
transitions; a cone over a cosimplicial object whose degree-zero leg is a limit fork is a limit
cone, which is the converse of the dual of Simplicial, Lemma 14.20.2. So both constructions are
limits of one diagram, and the comparison into the chosen limit is an isomorphism, naturally in the
sheaf on the total site.

## Main definitions

* `CategoryTheory.CosimplicialObject.isLimitOfIsLimitFork`: a cone over a cosimplicial object whose
  degree-zero leg is a limit fork of the two maps in degrees `0 ⇉ 1` is a limit cone. This is the
  converse of `CategoryTheory.CosimplicialObject.isLimitForkOfIsLimit`.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.restrictCone`: the direct image along the
  cocontinuous total functor, as a cone over the cosimplicial sheaf of the direct images of the
  components.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalPushforwardComparison`: the
  comparison of the two direct images, natural in the sheaf on the total site.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalPushforwardIso`: that comparison, as
  a natural isomorphism.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalInverseImageIso`: the same for the
  two inverse images, by uniqueness of adjoints.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.restrictConeIsLimit`: the direct image
  along the cocontinuous total functor is a limit of the cosimplicial sheaf of the direct images of
  the components.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.isIso_totalPushforwardComparison`: the
  comparison is an isomorphism in every sheaf.

## Implementation notes

Every statement here is written with the source topos spelled through the total topology of the
situation of `C`, which is the spelling of `totalMorphism` and of the whole fork development; the
crossing to the spelling of the cocontinuous morphism of topoi is definitional, and is taken once,
in the type of `totalPushforwardIso`.

The cone law of `restrictCone` is the cone law of Stacks 0D70 (3), conjugated by the
comparison of the two readings of the fork: the legs and transitions of that cone are stated with
the inverse image along a component inclusion, and the cosimplicial sheaf whose limit is the second
construction is stated with restriction to that component.

The comparison is built in the direction that lands in the limit, since naturality is then a
calculation on the legs; the isomorphism in the stated direction is its inverse.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] (X : SimplexCategory ⥤ A)

/-- **A cone over a cosimplicial object whose degree-zero leg is a limit fork is a limit cone.**
This is the converse of `CategoryTheory.CosimplicialObject.isLimitForkOfIsLimit`: a cone over the
whole simplex category is determined by its degree-zero leg, because every other leg is that leg
followed by the first vertex of its degree, and a map into the cone point is determined by its
composite with the degree-zero leg. -/
def isLimitOfIsLimitFork (c : Cone X)
    (hc : IsLimit (Fork.ofι (c.π.app (SimplexCategory.mk 0)) (cone_condition X c))) :
    IsLimit c where
  lift s := Fork.IsLimit.lift hc (s.π.app (SimplexCategory.mk 0)) (cone_condition X s)
  fac s n := by
    have h0 : Fork.IsLimit.lift hc (s.π.app (SimplexCategory.mk 0)) (cone_condition X s) ≫
        c.π.app (SimplexCategory.mk 0) = s.π.app (SimplexCategory.mk 0) :=
      Fork.IsLimit.lift_ι' hc _ _
    rw [← c.w (SimplexCategory.const (SimplexCategory.mk 0) n 0), ← Category.assoc, h0]
    exact s.w (SimplexCategory.const (SimplexCategory.mk 0) n 0)
  uniq s m hm := by
    refine Fork.IsLimit.hom_ext hc ?_
    have h0 : Fork.ι (Fork.ofι (c.π.app (SimplexCategory.mk 0)) (cone_condition X c)) =
      c.π.app (SimplexCategory.mk 0) := rfl
    rw [h0, hm (SimplexCategory.mk 0)]
    exact (Fork.IsLimit.lift_ι' hc _ _).symm

end CategoryTheory.CosimplicialObject

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

open CategoryTheory.SimplicialSiteSituation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.Augmentation D K)

/-- The cone law of the fork in restriction form: a leg of the fork, followed by a transition of
the fork, is again a leg. This is the cone law of Stacks 0D70 (3), conjugated by the
comparison of the two readings of the fork. -/
theorem restrictForkLeg_comp_restrictForkMap
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    restrictForkLeg a F m ≫ restrictForkMap a F φ = restrictForkLeg a F n := by
  refine (cancel_mono (restrictForkIso a F n).hom).mp ?_
  rw [Category.assoc, ← restrictForkIso_comp_totalForkTransition a F φ, ← Category.assoc,
    ← totalForkLeg_eq, ← totalForkLeg_eq]
  exact coneLaw a F φ

/-- The direct image along the cocontinuous functor out of the total category, as a cone over the
cosimplicial sheaf whose degree-`n` term is the direct image of the restriction to the component of
degree `n` along the augmentation of that degree. Its legs are the legs of the fork of
Stacks 0D70 (3), read through restriction to the components. -/
def restrictCone (F : Sheaf (situation C).totalTopology (Type u)) :
    Cone (SimplicialSiteSituation.Augmentation.pushforwardDiagram (situation C) D K a F) where
  pt := (totalMorphism a).pushforward.obj F
  π :=
    { app := fun n => restrictForkLeg a F n
      naturality := fun _ _ φ =>
        (Category.id_comp _).trans (restrictForkLeg_comp_restrictForkMap a F φ).symm }

/-- The degree-zero leg of `restrictCone` is a limit fork of the two vertex transitions: this is
the universal property of the fork of Stacks 0D70 (3), in restriction form. -/
def restrictConeForkIsLimit (F : Sheaf (situation C).totalTopology (Type u)) :
    IsLimit (Fork.ofι ((restrictCone a F).π.app (SimplexCategory.mk 0))
      (CosimplicialObject.cone_condition _ (restrictCone a F))) :=
  Fork.IsLimit.ofExistsUnique fun s => restrictFork_existsUnique a F s.pt s.ι (Fork.condition s)

/-- **The direct image along the cocontinuous total functor is a limit of the cosimplicial sheaf of
the direct images of the components.** Its degree-zero leg is a limit fork of the two vertex
transitions by Stacks 0D70 (3), and a cone over a cosimplicial object whose degree-zero leg is a
limit fork is a limit cone. -/
def restrictConeIsLimit (F : Sheaf (situation C).totalTopology (Type u)) :
    IsLimit (restrictCone a F) :=
  CosimplicialObject.isLimitOfIsLimitFork _ _ (restrictConeForkIsLimit a F)

/-- A leg of the fork in restriction form is natural in the sheaf on the total site. -/
theorem pushforward_map_comp_restrictForkLeg
    {F F' : Sheaf (situation C).totalTopology (Type u)} (α : F ⟶ F') (n : SimplexCategory) :
    (totalMorphism a).pushforward.map α ≫ restrictForkLeg a F' n =
      restrictForkLeg a F n ≫
        (componentAug a n).pushforward.map (((situation C).restrict n).map α) := by
  have hu : α ≫ (componentRestrictAdj n).unit.app F' =
      (componentRestrictAdj n).unit.app F ≫
        (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward.map
          (((situation C).restrict n).map α) :=
    (componentRestrictAdj n).unit.naturality α
  have hc := (componentCompIso a n).hom.naturality (((situation C).restrict n).map α)
  dsimp only [Functor.comp_map] at hc
  rw [restrictForkLeg, restrictForkLeg, ← CategoryTheory.Functor.map_comp_assoc, hu,
    CategoryTheory.Functor.map_comp_assoc, hc, Category.assoc]

/-- The comparison of the two direct images: into the limit of the cosimplicial sheaf, out of the
direct image along the cocontinuous total functor, through the cone `restrictCone`. -/
def totalPushforwardComparison :
    (totalMorphism a).pushforward ⟶
      SimplicialSiteSituation.Augmentation.pushforward (situation C) D K a where
  app F := SimplicialSiteSituation.Augmentation.pushforwardLiftCone (situation C) D K a
    (restrictCone a F)
  naturality F F' α := by
    refine SimplicialSiteSituation.Augmentation.pushforward_hom_ext (situation C) D K a
      fun n => ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine Eq.trans (congrArg (fun g => (totalMorphism a).pushforward.map α ≫ g)
      (SimplicialSiteSituation.Augmentation.pushforwardLiftCone_comp_projection
        (situation C) D K a (restrictCone a F') n)) ?_
    refine (pushforward_map_comp_restrictForkLeg a α n).trans ?_
    refine Eq.trans ?_ (congrArg (fun g =>
        SimplicialSiteSituation.Augmentation.pushforwardLiftCone (situation C) D K a
          (restrictCone a F) ≫ g)
      (SimplicialSiteSituation.Augmentation.pushforward_map_comp_projection
        (situation C) D K a α n).symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (fun g => g ≫
        (SimplicialSiteSituation.Augmentation.componentPushforward (situation C) D K a n).map α)
      (SimplicialSiteSituation.Augmentation.pushforwardLiftCone_comp_projection
        (situation C) D K a (restrictCone a F) n).symm

/-- The comparison of the two direct images is an isomorphism in every sheaf on the total site:
both cones are limits of the cosimplicial sheaf, and the comparison is a map of cones. -/
instance isIso_totalPushforwardComparison (F : Sheaf (situation C).totalTopology (Type u)) :
    IsIso ((totalPushforwardComparison a).app F) := by
  have hlim := limit.isLimit
    (SimplicialSiteSituation.Augmentation.pushforwardDiagram (situation C) D K a F)
  have h : (totalPushforwardComparison a).app F =
      (IsLimit.conePointUniqueUpToIso (restrictConeIsLimit a F) hlim).hom := by
    refine SimplicialSiteSituation.Augmentation.pushforward_hom_ext (situation C) D K a fun n => ?_
    exact (SimplicialSiteSituation.Augmentation.pushforwardLiftCone_comp_projection (situation C)
        D K a (restrictCone a F) n).trans
      (IsLimit.conePointUniqueUpToIso_hom_comp (restrictConeIsLimit a F) hlim n).symm
  rw [h]
  exact Iso.isIso_hom _

/-- **The two constructions of the direct image of a total augmentation agree.** For a case-(B)
simplicial-site situation the limit over the simplex category of the cosimplicial sheaf of the
direct images of the components is the direct image along the cocontinuous functor out of the total
category. -/
def totalPushforwardIso :
    SimplicialSiteSituation.Augmentation.pushforward (situation C) D K a ≅
      (totalMorphismOfTopoi a).pushforward :=
  (NatIso.ofComponents (fun F => asIso ((totalPushforwardComparison a).app F))
    fun α => (totalPushforwardComparison a).naturality α).symm

/-- **The two constructions of the inverse image of a total augmentation agree.** The descent of
the system of the inverse images along the component augmentations is the inverse image along the
cocontinuous functor out of the total category. The two are left adjoints of the two direct images,
which agree by `totalPushforwardIso`, so this is uniqueness of adjoints. -/
def totalInverseImageIso :
    SimplicialSiteSituation.Augmentation.inverseImage (situation C) D K a ≅
      (totalMorphismOfTopoi a).inverseImage :=
  Adjunction.leftAdjointUniq
    (SimplicialSiteSituation.Augmentation.adjunction (situation C) D K a)
    ((totalMorphismOfTopoi a).adj.ofNatIsoRight (totalPushforwardIso a).symm)

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end

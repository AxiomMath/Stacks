module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Augmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# The augmentation of the total site in the cocontinuous case

In the cocontinuous form of the simplicial-site situation an augmentation towards a site
`(D, K)` is a cocontinuous functor out of the degree-zero site which is compatible with every
vertex. Composing a vertex functor with it therefore gives a functor out of the site in each
simplicial degree which does not depend on the chosen vertex, and these assemble into a single
functor out of the total category. That functor is cocontinuous, so it induces a morphism of
topoi from the sheaves on the total site to the sheaves on `(D, K)`.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor`: the functor
  out of the total category which in simplicial degree `c` is the vertex functor followed by the
  augmentation.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalMorphismOfTopoi`: the induced
  morphism of topoi out of the total topos.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.ι_comp_totalAugmentationFunctor`: the
  inclusion of a component followed by the total functor is the augmentation of that component,
  as an equality of functors.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor_isCocontinuous`:
  the total functor is cocontinuous.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentPushforwardCompIso`: the
  direct image of the total augmentation, restricted along the inclusion of a component, is the
  direct image of the augmentation of that component.

## Implementation notes

The fibrewise functors are indexed by `SimplexCategoryᵒᵖ`, which is how the simplicial diagram of
categories is indexed; the vertex of a degree is the opposite of the constant map out of `[0]`.
The compatibility condition of the augmentation says exactly that composing a vertex functor with
the augmentation is independent of the vertex, and that is what identifies the transition of the
fibrewise family with an equality of functors rather than with a natural isomorphism. Because the
transitions are transports along equalities, the unit and cocycle coherences of the family hold by
proof irrelevance, and the functor out of the total category is assembled by
`CategoryTheory.Grothendieck.functorFromOfEq`.

Cocontinuity is reduced to cocontinuity in each simplicial degree: a covering sieve of the target
pulls back, along the fibrewise functor, to a covering sieve of the component, and the inclusion of
a component into the total site preserves covering sieves because it is continuous.

The compatibility of the direct images is then two applications of the composition comparison of
direct images along cocontinuous functors, separated by the transport along the equality of site
functors; no further coherence is needed, because that equality holds on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace CocontinuousSimplicialSite

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-- The opposite of the vertex of a simplicial degree: the degree-zero object sits over every
degree by the constant map, and the diagram of categories is indexed by the opposite simplex
category. -/
def degreeZeroVertexOp (c : SimplexCategoryᵒᵖ) : c ⟶ Opposite.op (SimplexCategory.mk 0) :=
  (SimplexCategory.const (SimplexCategory.mk 0) c.unop 0).op

namespace Augmentation

variable (a : C.Augmentation D K)

/-- The functor out of the site in simplicial degree `c` attached to an augmentation: the vertex
functor of that degree followed by the augmentation. -/
def totalAugmentationFibre (c : SimplexCategoryᵒᵖ) : (C.underlying.obj c) ⥤ D :=
  (C.underlying.map (degreeZeroVertexOp c)).toFunctor ⋙ a.functor

/-- The fibrewise functors of an augmentation are compatible with the simplicial diagram: this is
the compatibility condition of the augmentation, read at the vertex of the source degree. -/
theorem totalAugmentationFibre_eq {c c' : SimplexCategoryᵒᵖ} (f : c ⟶ c') :
    totalAugmentationFibre a c =
      (C.underlying.map f).toFunctor ⋙ totalAugmentationFibre a c' := by
  dsimp only [totalAugmentationFibre]
  rw [← Functor.assoc, ← Cat.Hom.comp_toFunctor, ← C.underlying.map_comp]
  exact (a.compatibility c.unop (f ≫ degreeZeroVertexOp c').unop
    (SimplexCategory.const (SimplexCategory.mk 0) c.unop 0)).symm

/-- The unit coherence of the fibrewise family: both sides are transports along equalities of
functors, so they agree by proof irrelevance. -/
theorem totalAugmentationFibre_eq_id (c : SimplexCategoryᵒᵖ) :
    eqToHom (totalAugmentationFibre_eq a (𝟙 c)) =
      eqToHom (Grothendieck.fib_map_id_eq (totalAugmentationFibre a) c) :=
  rfl

/-- The cocycle coherence of the fibrewise family: every transition is a transport along an
equality of functors, so the two sides agree componentwise. -/
theorem totalAugmentationFibre_eq_comp (c₁ c₂ c₃ : SimplexCategoryᵒᵖ) (f : c₁ ⟶ c₂)
    (g : c₂ ⟶ c₃) :
    eqToHom (totalAugmentationFibre_eq a (f ≫ g)) =
      eqToHom (totalAugmentationFibre_eq a f) ≫
        Functor.whiskerLeft (C.underlying.map f).toFunctor
            (eqToHom (totalAugmentationFibre_eq a g)) ≫
          eqToHom (Grothendieck.fib_map_comp_eq (totalAugmentationFibre a) f g) := by
  ext X
  simp [eqToHom_app]

/-- The functor out of the total category attached to an augmentation: in simplicial degree `c` it
is the vertex functor of that degree followed by the augmentation. -/
def totalAugmentationFunctor : Grothendieck C.underlying ⥤ D :=
  Grothendieck.functorFromOfEq (totalAugmentationFibre a)
    (fun {_ _} f => eqToHom (totalAugmentationFibre_eq a f))
    (totalAugmentationFibre_eq_id a) (totalAugmentationFibre_eq_comp a)

/-- The inclusion of the component in simplicial degree `c`, followed by the functor out of the
total category, is the functor attached to that degree. -/
theorem ι_comp_totalAugmentationFunctor (c : SimplexCategoryᵒᵖ) :
    Grothendieck.ι C.underlying c ⋙ totalAugmentationFunctor a =
      totalAugmentationFibre a c := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun y z f => ?_
  simp only [Functor.comp_map, totalAugmentationFunctor, Grothendieck.functorFromOfEq,
    Grothendieck.ι, eqToHom_app, CategoryTheory.Functor.map_comp]
  rw [eqToHom_comp_map_eqToHom_assoc]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The functor out of the total category sends an arrow of one component to the image of that
arrow under the functor attached to the component's degree. -/
theorem totalAugmentationFunctor_map_ι {c : SimplexCategoryᵒᵖ} {y z : C.underlying.obj c}
    (g : y ⟶ z) :
    (totalAugmentationFunctor a).map ((Grothendieck.ι C.underlying c).map g) =
      (totalAugmentationFibre a c).map g :=
  (Functor.congr_hom (ι_comp_totalAugmentationFunctor a c) g).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- Pulling a sieve back along the functor attached to a component is the same as pulling it back
along the functor out of the total category and then along the inclusion of that component. -/
theorem functorPullback_totalAugmentationFunctor {c : SimplexCategoryᵒᵖ}
    {x : C.underlying.obj c} (S : Sieve ((totalAugmentationFunctor a).obj ⟨c, x⟩)) :
    Sieve.functorPullback (totalAugmentationFibre a c) S =
      Sieve.functorPullback (Grothendieck.ι C.underlying c)
        (Sieve.functorPullback (totalAugmentationFunctor a) S) :=
  Sieve.ext fun _ g =>
    Iff.of_eq (congrArg (fun h => S.arrows h) (totalAugmentationFunctor_map_ι a g)).symm

/-- The functor attached to a simplicial degree is cocontinuous, being a vertex functor of the
simplicial diagram followed by the augmentation. -/
theorem totalAugmentationFibre_isCocontinuous (c : SimplexCategoryᵒᵖ) :
    (totalAugmentationFibre a c).IsCocontinuous (topologyOfCoverings (C.coverage c)) K := by
  have h1 : ((C.underlying.map (degreeZeroVertexOp c)).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage c))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
    C.isCocontinuous (degreeZeroVertexOp c)
  have h2 : a.functor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
    a.isCocontinuous
  exact isCocontinuous_comp
    (C.underlying.map (degreeZeroVertexOp c)).toFunctor a.functor
    (topologyOfCoverings (C.coverage c))
    (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0))))

/-- The functor out of the total category is cocontinuous: a covering sieve of the target pulls
back to a covering sieve of the component containing the given object, and the inclusion of a
component preserves covering sieves. -/
theorem totalAugmentationFunctor_isCocontinuous :
    (totalAugmentationFunctor a).IsCocontinuous
      (SimplicialCoverings.totalTopology C.underlying C.coverage) K := by
  constructor
  rintro ⟨b, x⟩ S hS
  have h1 : Sieve.functorPullback (totalAugmentationFibre a b) S ∈
      topologyOfCoverings (C.coverage b) x :=
    (totalAugmentationFibre_isCocontinuous a b).cover_lift hS
  rw [functorPullback_totalAugmentationFunctor] at h1
  have hcont : (Grothendieck.ι C.underlying b).IsContinuous
      (topologyOfCoverings (C.coverage b))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) b.unop
  exact GrothendieckTopology.superset_covering _
    ((Sieve.functorPushforward_le_iff_le_functorPullback _ _ _).mpr le_rfl)
    ((CoverPreserving.of_isContinuous (Grothendieck.ι C.underlying b)
      (topologyOfCoverings (C.coverage b))
      (SimplicialCoverings.totalTopology C.underlying C.coverage)).cover_preserve h1)

/-- The morphism of topoi from the sheaves on the total site to the sheaves on the augmentation
site, induced by the cocontinuous functor out of the total category. -/
def totalMorphismOfTopoi :
    MorphismOfTopoi
      (Sheaf (SimplicialCoverings.totalTopology C.underlying C.coverage) (Type u))
      (Sheaf K (Type u)) :=
  haveI := totalAugmentationFunctor_isCocontinuous a
  { pushforward := gStar _ _ (SimplicialCoverings.totalTopology C.underlying C.coverage) K
      (totalAugmentationFunctor a)
    inverseImage := gInv _ _ (SimplicialCoverings.totalTopology C.underlying C.coverage) K
      (totalAugmentationFunctor a)
    adj := gAdjunction _ _
      (SimplicialCoverings.totalTopology C.underlying C.coverage) K (totalAugmentationFunctor a)
    preservesFiniteLimits := main_left_exact _ _
      (SimplicialCoverings.totalTopology C.underlying C.coverage) K
      (totalAugmentationFunctor a) }

/-- The direct image along the total augmentation, restricted along the inclusion of the component
in simplicial degree `c`, is the direct image along the augmentation of that component. -/
def componentPushforwardCompIso (c : SimplexCategoryᵒᵖ) :
    haveI := totalAugmentationFunctor_isCocontinuous a
    haveI : (Grothendieck.ι C.underlying c).IsCocontinuous (topologyOfCoverings (C.coverage c))
        (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
      SimplicialSiteSituation.componentFunctor_isCocontinuous
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) c.unop
    haveI : ((C.underlying.map (degreeZeroVertexOp c)).toFunctor).IsCocontinuous
        (topologyOfCoverings (C.coverage c))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
      C.isCocontinuous (degreeZeroVertexOp c)
    haveI : a.functor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
      a.isCocontinuous
    (Grothendieck.ι C.underlying c).sheafPushforwardCocontinuous (Type u)
        (topologyOfCoverings (C.coverage c))
        (SimplicialCoverings.totalTopology C.underlying C.coverage) ⋙
      (totalAugmentationFunctor a).sheafPushforwardCocontinuous (Type u)
        (SimplicialCoverings.totalTopology C.underlying C.coverage) K ≅
    (C.underlying.map (degreeZeroVertexOp c)).toFunctor.sheafPushforwardCocontinuous (Type u)
        (topologyOfCoverings (C.coverage c))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) ⋙
      a.functor.sheafPushforwardCocontinuous (Type u)
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K := by
  haveI := totalAugmentationFunctor_isCocontinuous a
  haveI : (Grothendieck.ι C.underlying c).IsCocontinuous (topologyOfCoverings (C.coverage c))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) :=
    SimplicialSiteSituation.componentFunctor_isCocontinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) c.unop
  haveI : ((C.underlying.map (degreeZeroVertexOp c)).toFunctor).IsCocontinuous
      (topologyOfCoverings (C.coverage c))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
    C.isCocontinuous (degreeZeroVertexOp c)
  haveI : a.functor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
    a.isCocontinuous
  haveI := totalAugmentationFibre_isCocontinuous a c
  haveI : (Grothendieck.ι C.underlying c ⋙ totalAugmentationFunctor a).IsCocontinuous
      (topologyOfCoverings (C.coverage c)) K := by
    rw [ι_comp_totalAugmentationFunctor]
    exact totalAugmentationFibre_isCocontinuous a c
  exact (sheafPushforwardCocontinuousCompIso (topologyOfCoverings (C.coverage c))
      (SimplicialCoverings.totalTopology C.underlying C.coverage) K
      (Grothendieck.ι C.underlying c) (totalAugmentationFunctor a)).symm ≪≫
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u}
      (topologyOfCoverings (C.coverage c)) K (ι_comp_totalAugmentationFunctor a c) ≪≫
    sheafPushforwardCocontinuousCompIso (topologyOfCoverings (C.coverage c))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K
      (C.underlying.map (degreeZeroVertexOp c)).toFunctor a.functor

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentedMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism

/-!
# The total square of a morphism of augmented simplicial sites

Two simplicial sites in the cocontinuous case, each carrying an augmentation towards a site, and
a morphism between them whose degree-zero component is compatible with the two augmentations
through a morphism of the augmentation sites, together determine a square of topoi: the total
topoi along the top, the augmentation topoi along the bottom, the total morphism of the two
simplicial sites along the top, and the morphism of augmentation topoi along the bottom. That
square commutes.

The commutation already holds at the level of site functors: the functor out of the total
category attached to an augmentation, followed by the functor between the augmentation sites, is
the functor between the total categories followed by the functor attached to the second
augmentation. Both sides are cocontinuous, so the square of direct images follows from the
composition comparison of direct images along cocontinuous functors.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalAugmentationFibre_comp`: in every
  simplicial degree the square of site functors commutes.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalFunctor_comp_totalAugmentationFunctor`:
  the same square for the functors out of the total categories.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.totalAugmentationPushforwardIso`: the
  square of topoi commutes, as a natural isomorphism of direct-image functors.

## Implementation notes

The source writes an equality of morphisms of topoi. Since composition of the associated sheaf
functors is only canonical up to isomorphism, the square is expressed, as for the degree-zero
square of Tag 0D98 and the component squares of Tag 0D96, by an isomorphism of direct-image
functors.

Only the cocontinuous case is treated, because the total morphism of a morphism between
simplicial sites is available only there. In that case the morphism of topoi out of the total
topos attached to an augmentation is induced by a cocontinuous functor out of the total category,
which is what makes the square reduce to an equality of site functors.

The degree-zero compatibility propagates to every simplicial degree exactly as in the source: the
functor attached to a simplicial degree is the vertex functor of that degree followed by the
augmentation, so the square of that degree is the degree-zero square precomposed with the vertex
functor, which the morphism between the simplicial sites commutes with.

## References

* [Stacks Project, Tag 0D99](https://stacks.math.columbia.edu/tag/0D99)
* [Stacks Project, Tag 0D98](https://stacks.math.columbia.edu/tag/0D98)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

namespace CocontinuousSimplicialSite.Morphism

attribute [local implicit_reducible] CocontinuousSimplicialSite.Morphism.totalFunctor
  CocontinuousSimplicialSite.Augmentation.totalAugmentationFunctor
  Grothendieck.functorFromOfEq Grothendieck.map

variable {C C' : CocontinuousSimplicialSite.{u}} {D D' : Cat.{u, u}}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}

/-- In every simplicial degree, the functor attached to an augmentation followed by a functor
between the augmentation sites is the degreewise functor of a morphism between the simplicial
sites followed by the functor attached to the second augmentation, as soon as the two agree in
degree zero. -/
theorem totalAugmentationFibre_comp (h : CocontinuousSimplicialSite.Morphism C C')
    (a : C.Augmentation D K) (a' : C'.Augmentation D' K') (v : D ⥤ D')
    (hv : a.functor ⋙ v =
      (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor)
    (c : SimplexCategoryᵒᵖ) :
    Augmentation.totalAugmentationFibre a c ⋙ v =
      (h.hom.app c).toFunctor ⋙ Augmentation.totalAugmentationFibre a' c := by
  dsimp only [Augmentation.totalAugmentationFibre]
  rw [Functor.assoc, hv]
  rw [show ((C.underlying.map (degreeZeroVertexOp c)).toFunctor ⋙
      ((h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor)) =
      ((C.underlying.map (degreeZeroVertexOp c)).toFunctor ⋙
      (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor) ⋙ a'.functor from rfl]
  rw [← Cat.Hom.comp_toFunctor, h.hom.naturality, Cat.Hom.comp_toFunctor, Functor.assoc]

/-- The functor between the total categories followed by the functor attached to an augmentation
of the target sends an arrow of the total category to the transition of the fibrewise family,
followed by the image of the arrow inside its own simplicial degree. -/
theorem totalFunctor_totalAugmentationFunctor_map
    (h : CocontinuousSimplicialSite.Morphism C C') (a' : C'.Augmentation D' K')
    {X Y : Grothendieck C.underlying} (f : X ⟶ Y) :
    (h.totalFunctor ⋙ Augmentation.totalAugmentationFunctor a').map f =
      (eqToHom (Augmentation.totalAugmentationFibre_eq a' f.base)).app
          ((h.hom.app X.base).toFunctor.obj X.fiber) ≫
        (Augmentation.totalAugmentationFibre a' Y.base).map
          ((eqToHom (h.hom.naturality f.base).symm).toNatTrans.app X.fiber ≫
            (h.hom.app Y.base).toFunctor.map f.fiber) :=
  rfl

/-- The functor attached to an augmentation followed by a functor out of the augmentation site
sends an arrow of the total category to the image of the transition of the fibrewise family
followed by the image of the arrow inside its own simplicial degree. -/
theorem totalAugmentationFunctor_comp_map (a : C.Augmentation D K) (v : D ⥤ D')
    {X Y : Grothendieck C.underlying} (f : X ⟶ Y) :
    (Augmentation.totalAugmentationFunctor a ⋙ v).map f =
      v.map ((eqToHom (Augmentation.totalAugmentationFibre_eq a f.base)).app X.fiber ≫
        (Augmentation.totalAugmentationFibre a Y.base).map f.fiber) :=
  rfl

/-- The two composites of site functors out of the total category agree on objects: on an object
of the component of a simplicial degree this is the square of site functors of that degree. -/
theorem totalFunctor_comp_totalAugmentationFunctor_obj
    (h : CocontinuousSimplicialSite.Morphism C C')
    (a : C.Augmentation D K) (a' : C'.Augmentation D' K') (v : D ⥤ D')
    (hv : a.functor ⋙ v =
      (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor)
    (X : Grothendieck C.underlying) :
    (h.totalFunctor ⋙ Augmentation.totalAugmentationFunctor a').obj X =
      (Augmentation.totalAugmentationFunctor a ⋙ v).obj X :=
  (CategoryTheory.Functor.congr_obj
    (totalAugmentationFibre_comp h a a' v hv X.base) X.fiber).symm

/-- The functor between the total categories followed by the functor attached to an augmentation
of the target is the functor attached to the augmentation of the source followed by the functor
between the augmentation sites. -/
theorem totalFunctor_comp_totalAugmentationFunctor
    (h : CocontinuousSimplicialSite.Morphism C C')
    (a : C.Augmentation D K) (a' : C'.Augmentation D' K') (v : D ⥤ D')
    (hv : a.functor ⋙ v =
      (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor) :
    h.totalFunctor ⋙ Augmentation.totalAugmentationFunctor a' =
      Augmentation.totalAugmentationFunctor a ⋙ v := by
  refine CategoryTheory.Functor.ext
    (totalFunctor_comp_totalAugmentationFunctor_obj h a a' v hv) (fun X Y f => ?_)
  have hm := CategoryTheory.Functor.congr_hom
    (totalAugmentationFibre_comp h a a' v hv Y.base) f.fiber
  rw [totalFunctor_totalAugmentationFunctor_map, totalAugmentationFunctor_comp_map]
  simp only [CategoryTheory.Functor.map_comp, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    eqToHom_map]
  simp only [← Functor.comp_map]
  rw [hm]
  simp

/-- **Stacks 0D99.** Let a morphism between simplicial sites, augmentations of its source and its
target, and a morphism of the augmentation topoi compatible with them be given. Then the square
formed by the total topoi, the augmentation topoi, the total morphism of the simplicial sites and
that morphism of the augmentation topoi commutes, as witnessed by a natural isomorphism of
direct-image functors. -/
@[stacks 0D99]
noncomputable def totalAugmentationPushforwardIso
    (h : CocontinuousSimplicialSite.Morphism C C')
    (a : C.Augmentation D K) (a' : C'.Augmentation D' K')
    (g : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf K' (Type u)))
    (hg : SimplicialSiteMorphism.CompatibleWithAugmentations
      (SimplicialSiteMorphism.ofCocontinuous h) a a' g) :
    h.totalMorphism.pushforward ⋙ (Augmentation.totalMorphismOfTopoi a').pushforward ≅
      (Augmentation.totalMorphismOfTopoi a).pushforward ⋙ g.pushforward := by
  change ∃ (v : D ⥤ D') (hv : v.IsCocontinuous K K'),
    (g = cocontinuousMorphismOfTopoi v hv) ∧
      (a.functor ⋙ v =
        (h.hom.app (Opposite.op (SimplexCategory.mk 0))).toFunctor ⋙ a'.functor) at hg
  let v := Classical.choose hg
  let hv := Classical.choose (Classical.choose_spec hg)
  have ⟨hgeq, hcomp⟩ := Classical.choose_spec (Classical.choose_spec hg)
  rw [hgeq]
  let Jtot := SimplicialCoverings.totalTopology C.underlying C.coverage
  let Jtot' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  letI : h.totalFunctor.IsCocontinuous Jtot Jtot' := h.totalFunctor_isCocontinuous
  letI : (Augmentation.totalAugmentationFunctor a).IsCocontinuous Jtot K :=
    Augmentation.totalAugmentationFunctor_isCocontinuous a
  letI : (Augmentation.totalAugmentationFunctor a').IsCocontinuous Jtot' K' :=
    Augmentation.totalAugmentationFunctor_isCocontinuous a'
  letI : v.IsCocontinuous K K' := hv
  letI : (h.totalFunctor ⋙ Augmentation.totalAugmentationFunctor a').IsCocontinuous Jtot K' :=
    CategoryTheory.isCocontinuous_comp _ _ Jtot Jtot'
  letI : (Augmentation.totalAugmentationFunctor a ⋙ v).IsCocontinuous Jtot K' :=
    CategoryTheory.isCocontinuous_comp _ _ Jtot K
  change h.totalFunctor.sheafPushforwardCocontinuous (Type u) Jtot Jtot' ⋙
      (Augmentation.totalAugmentationFunctor a').sheafPushforwardCocontinuous
        (Type u) Jtot' K' ≅
    (Augmentation.totalAugmentationFunctor a).sheafPushforwardCocontinuous (Type u) Jtot K ⋙
      v.sheafPushforwardCocontinuous (Type u) K K'
  exact (sheafPushforwardCocontinuousCompIso Jtot Jtot' K' h.totalFunctor
      (Augmentation.totalAugmentationFunctor a')).symm ≪≫
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} Jtot K'
      (totalFunctor_comp_totalAugmentationFunctor h a a' v hcomp) ≪≫
    sheafPushforwardCocontinuousCompIso Jtot K K' (Augmentation.totalAugmentationFunctor a) v

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end

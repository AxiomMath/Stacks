module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents

/-!
# The fork of the total augmentation, reduced

In the cocontinuous simplicial-site situation the total augmentation comes with a fork whose
legs are the canonical maps from the total direct image to the direct images of the components,
and whose comparison maps are the transitions of those direct images. The cone law asserts that
every leg composed with a transition is again a leg. This file reduces that law, without proving
it, to a form in which two of its ingredients have cancelled.

Both reductions are purely formal, so they are stated for an arbitrary comparison of direct
images of morphisms of topoi and then instantiated.

## Main definitions

* `MorphismOfTopoi.forkLeg`: the leg of such a fork, built from the unit of an adjunction
  `g^{-1} ⊣ g_*` and a comparison `g_* ⋙ A_* ≅ B_*`.
* `MorphismOfTopoi.forkLegOfRestriction`: the same leg read through an identification of `g^{-1}`
  with a restriction functor.

## Main results

* `MorphismOfTopoi.forkLaw_iff`: the cone law over two identifications of the inverse images with
  restriction functors is equivalent to the cone law in which those identifications have
  cancelled.
* `MorphismOfTopoi.forkLeg_ofNatIsoLeft`: a leg depends on the chosen adjunction `g^{-1} ⊣ g_*`,
  and changing that adjunction by a natural automorphism of `g^{-1}` postcomposes the leg with
  the direct image of that automorphism.
* `MorphismOfTopoi.forkLaw_forces`: consequently a cone law which holds for every adjunction
  forces that automorphism to act trivially on the comparison.
* `MorphismOfTopoi.forkLaw_of_comparison` and
  `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_of_comparison`: the cone law
  follows from two named obligations about a comparison of the direct image along a composite
  with the direct image along the inclusion of the target degree. Neither obligation is
  discharged here and the comparison is not constructed.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentDirectImageTransitionMap_eq`:
  the transition on the direct images of the components does not depend on the adjunction of the
  simplicial transition morphism: it is the direct-image restriction transition conjugated by the
  identifications of the inverse images with the restrictions.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_iff_restrictForm`: the cone law
  for the total augmentation, reduced.

## Implementation notes

The transition on direct images is defined as the mate, under the topos adjunction of the
simplicial transition, of a map built from the inverse-image restriction transition; and the
inverse-image restriction transition is itself defined as a mate under the same adjunction. The
two transpositions cancel, so the adjunction leaves the transition map entirely: that is
`componentDirectImageTransitionMap_eq`, and it is why no mate of that adjunction has to be
constructed. What does *not* cancel is the adjunction of the component inclusion, which enters
the legs through its unit and enters nothing else; `forkLeg_ofNatIsoLeft` measures exactly how
the legs move with it.

`forkLaw_iff` cancels the two identifications `g^{-1} ≅ restrict` because the direct image of
the one in the target degree is an isomorphism and appears on both sides. The remaining law is
stated over `forkLegOfRestriction`, i.e. over the unit of the adjunction `restrict ⊣ g_*`
obtained by transporting the given adjunction along that identification.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u'' v₃ u₃

namespace MorphismOfTopoi

variable {T : Type u} [Category.{v} T] {Dd : Type u'} [Category.{v'} Dd]
  {Cm : Type u''} [Category.{v''} Cm] {Cn : Type u₃} [Category.{v₃} Cn]

/-- Naturality of a comparison `G ⋙ H ≅ B`, with the composite functor unfolded. -/
private theorem map_map_comp_hom_app {G : Cm ⥤ T} {H : T ⥤ Dd} {B : Cm ⥤ Dd}
    (p : G ⋙ H ≅ B) {X Y : Cm} (x : X ⟶ Y) :
    H.map (G.map x) ≫ p.hom.app Y = p.hom.app X ≫ B.map x :=
  p.hom.naturality x

/-- A leg of the fork comparing the direct image along `A` with the direct images along the
composites `A ∘ g`: the direct image of the adjunction unit of `g`, followed by a comparison of
`g_* ⋙ A_*` with a given functor. -/
def forkLeg (A : MorphismOfTopoi T Dd) (g : MorphismOfTopoi Cm T) (B : Cm ⥤ Dd)
    (p : g.pushforward ⋙ A.pushforward ≅ B) (adj : g.inverseImage ⊣ g.pushforward) (F : T) :
    A.pushforward.obj F ⟶ B.obj (g.inverseImage.obj F) :=
  A.pushforward.map (adj.unit.app F) ≫ p.hom.app (g.inverseImage.obj F)

/-- The same leg read through an identification `e : g^{-1} ≅ R` of the inverse image with a
restriction functor: it is built from the unit of the adjunction `R ⊣ g_*` obtained by
transporting `adj` along `e`. -/
def forkLegOfRestriction (A : MorphismOfTopoi T Dd) (g : MorphismOfTopoi Cm T) (B : Cm ⥤ Dd)
    (p : g.pushforward ⋙ A.pushforward ≅ B) {R : T ⥤ Cm} (e : g.inverseImage ≅ R)
    (adj : g.inverseImage ⊣ g.pushforward) (F : T) :
    A.pushforward.obj F ⟶ B.obj (R.obj F) :=
  A.pushforward.map (adj.unit.app F ≫ g.pushforward.map (e.hom.app F)) ≫ p.hom.app (R.obj F)

/-- The two readings of a leg differ by the direct image of the identification. -/
theorem forkLeg_eq_forkLegOfRestriction (A : MorphismOfTopoi T Dd) (g : MorphismOfTopoi Cm T)
    (B : Cm ⥤ Dd) (p : g.pushforward ⋙ A.pushforward ≅ B) {R : T ⥤ Cm}
    (e : g.inverseImage ≅ R) (adj : g.inverseImage ⊣ g.pushforward) (F : T) :
    forkLeg A g B p adj F = forkLegOfRestriction A g B p e adj F ≫ B.map (e.inv.app F) := by
  have hnat := map_map_comp_hom_app p (e.hom.app F)
  dsimp only [forkLeg, forkLegOfRestriction]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, hnat]
  simp [← CategoryTheory.Functor.map_comp]

/-- A leg is built from the unit of an adjunction `g^{-1} ⊣ g_*`, and it moves with the choice of
that adjunction: transporting the adjunction along a natural automorphism `c` of `g^{-1}`
postcomposes the leg with the direct image of `c`. -/
theorem forkLeg_ofNatIsoLeft (A : MorphismOfTopoi T Dd) (g : MorphismOfTopoi Cm T) (B : Cm ⥤ Dd)
    (p : g.pushforward ⋙ A.pushforward ≅ B) (adj : g.inverseImage ⊣ g.pushforward)
    (c : g.inverseImage ≅ g.inverseImage) (F : T) :
    forkLeg A g B p (adj.ofNatIsoLeft c) F = forkLeg A g B p adj F ≫ B.map (c.hom.app F) := by
  have hnat := map_map_comp_hom_app p (c.hom.app F)
  dsimp only [forkLeg]
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_comp, Category.assoc, hnat]

/-- The cone law over two identifications of the inverse images with restriction functors is
equivalent to the cone law in which those identifications have cancelled. -/
theorem forkLaw_iff (A : MorphismOfTopoi T Dd) (gm : MorphismOfTopoi Cm T)
    (gn : MorphismOfTopoi Cn T) (f : MorphismOfTopoi Cn Cm) (Bm : Cm ⥤ Dd) (Bn : Cn ⥤ Dd)
    (pm : gm.pushforward ⋙ A.pushforward ≅ Bm)
    (pn : gn.pushforward ⋙ A.pushforward ≅ Bn) (t : f.pushforward ⋙ Bm ≅ Bn)
    {Rm : T ⥤ Cm} {Rn : T ⥤ Cn} (em : gm.inverseImage ≅ Rm) (en : gn.inverseImage ≅ Rn)
    (rt : Rm ⟶ Rn ⋙ f.pushforward) (adjm : gm.inverseImage ⊣ gm.pushforward)
    (adjn : gn.inverseImage ⊣ gn.pushforward) (F : T) :
    (forkLeg A gm Bm pm adjm F ≫
        Bm.map (em.hom.app F ≫ rt.app F ≫ f.pushforward.map (en.inv.app F)) ≫
          t.hom.app (gn.inverseImage.obj F) = forkLeg A gn Bn pn adjn F) ↔
      (forkLegOfRestriction A gm Bm pm em adjm F ≫
          Bm.map (rt.app F) ≫ t.hom.app (Rn.obj F) =
        forkLegOfRestriction A gn Bn pn en adjn F) := by
  have htn := map_map_comp_hom_app t (en.inv.app F)
  have key : forkLeg A gm Bm pm adjm F ≫
      Bm.map (em.hom.app F ≫ rt.app F ≫ f.pushforward.map (en.inv.app F)) ≫
        t.hom.app (gn.inverseImage.obj F) =
      (forkLegOfRestriction A gm Bm pm em adjm F ≫
          Bm.map (rt.app F) ≫ t.hom.app (Rn.obj F)) ≫ Bn.map (en.inv.app F) := by
    rw [forkLeg_eq_forkLegOfRestriction A gm Bm pm em adjm F]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [htn]
    simp only [← Category.assoc]
    congr 2
    simp [← CategoryTheory.Functor.map_comp]
  rw [key, forkLeg_eq_forkLegOfRestriction A gn Bn pn en adjn F]
  exact ⟨fun h => (cancel_mono (Bn.map (en.inv.app F))).mp h, fun h => by rw [h]⟩

/-- The cone law in restriction form follows from two named obligations: a comparison `θ` of the
direct image along the composite `g_m ∘ f` with the direct image along `g_n`, which must be
compatible with the two comparisons and the transition (`h1`), and a unit law for `θ` in the
source topos (`h2`). Nothing here is specific to the simplicial situation, and `θ` is not
constructed: both obligations are hypotheses. -/
theorem forkLaw_of_comparison (A : MorphismOfTopoi T Dd) (gm : MorphismOfTopoi Cm T)
    (gn : MorphismOfTopoi Cn T) (f : MorphismOfTopoi Cn Cm) (Bm : Cm ⥤ Dd) (Bn : Cn ⥤ Dd)
    (pm : gm.pushforward ⋙ A.pushforward ≅ Bm)
    (pn : gn.pushforward ⋙ A.pushforward ≅ Bn) (t : f.pushforward ⋙ Bm ≅ Bn)
    {Rm : T ⥤ Cm} {Rn : T ⥤ Cn} (em : gm.inverseImage ≅ Rm) (en : gn.inverseImage ≅ Rn)
    (rt : Rm ⟶ Rn ⋙ f.pushforward) (adjm : gm.inverseImage ⊣ gm.pushforward)
    (adjn : gn.inverseImage ⊣ gn.pushforward) (F : T)
    (θ : f.pushforward ⋙ gm.pushforward ⟶ gn.pushforward)
    (h1 : pm.hom.app (f.pushforward.obj (Rn.obj F)) ≫ t.hom.app (Rn.obj F) =
      A.pushforward.map (θ.app (Rn.obj F)) ≫ pn.hom.app (Rn.obj F))
    (h2 : (adjm.unit.app F ≫ gm.pushforward.map (em.hom.app F)) ≫
        gm.pushforward.map (rt.app F) ≫ θ.app (Rn.obj F) =
      adjn.unit.app F ≫ gn.pushforward.map (en.hom.app F)) :
    forkLegOfRestriction A gm Bm pm em adjm F ≫
        Bm.map (rt.app F) ≫ t.hom.app (Rn.obj F) =
      forkLegOfRestriction A gn Bn pn en adjn F := by
  have hnat := map_map_comp_hom_app pm (rt.app F)
  dsimp only [forkLegOfRestriction]
  rw [Category.assoc, ← reassoc_of% hnat, h1, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, Category.assoc, h2]

/-- A cone law which holds for *every* adjunction `g_m^{-1} ⊣ g_{m,*}` forces every natural
automorphism of `g_m^{-1}` to act trivially on the comparison it is composed with. Only the legs
depend on that adjunction, so a law relating a leg in one degree to a leg in another constrains
the two adjunctions against each other. -/
theorem forkLaw_forces (A : MorphismOfTopoi T Dd) (gm : MorphismOfTopoi Cm T)
    (gn : MorphismOfTopoi Cn T) (Bm : Cm ⥤ Dd) (Bn : Cn ⥤ Dd)
    (pm : gm.pushforward ⋙ A.pushforward ≅ Bm)
    (pn : gn.pushforward ⋙ A.pushforward ≅ Bn) (adjm : gm.inverseImage ⊣ gm.pushforward)
    (adjn : gn.inverseImage ⊣ gn.pushforward) (F : T)
    (d : Bm.obj (gm.inverseImage.obj F) ⟶ Bn.obj (gn.inverseImage.obj F))
    (h : ∀ adj : gm.inverseImage ⊣ gm.pushforward, forkLeg A gm Bm pm adj F ≫ d =
      forkLeg A gn Bn pn adjn F)
    (c : gm.inverseImage ≅ gm.inverseImage) :
    forkLeg A gm Bm pm adjm F ≫ Bm.map (c.hom.app F) ≫ d =
      forkLeg A gm Bm pm adjm F ≫ d := by
  rw [← Category.assoc, ← forkLeg_ofNatIsoLeft, h (adjm.ofNatIsoLeft c), h adjm]

end MorphismOfTopoi

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
variable (a : C.Augmentation D K)

/-- Inverse image along the inclusion of a simplicial component is restriction to that
component, as a natural isomorphism of functors. This is Mathlib's comparison of the two
constructions for a functor that is both continuous and cocontinuous, read at the component
inclusion; no second name is introduced for it. -/
def componentInverseImageRestrictIso (k : SimplexCategory) :
    (SimplicialSiteSituation.componentMorphism (situation C) k).inverseImage ≅
      (situation C).restrict k :=
  ((situation C).inclusion k).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type u) ((situation C).componentTopology k) (situation C).totalTopology

/-- The leg of the fork is the generic one, at the comparison of the total augmentation with the
augmentation of the component and at the chosen adjunction of the component inclusion. -/
theorem totalComponentUnitMap_eq_forkLeg (m : SimplexCategory)
    (F : Sheaf (situation C).totalTopology (Type u)) :
    totalComponentUnitMap a F m =
      MorphismOfTopoi.forkLeg (totalMorphismOfTopoi a)
        (SimplicialSiteSituation.componentMorphism (situation C) m)
        (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a m).pushforward
        (componentInclusionCompPushforwardIso a m)
        (SimplicialSiteSituation.componentMorphism (situation C) m).adj F :=
  rfl

/-- The transition on the direct images of the components does not depend on the adjunction of
the simplicial transition morphism. It is defined as a mate under that adjunction of a map built
from the inverse-image restriction transition, which is itself a mate under the same adjunction;
the two transpositions cancel, leaving the direct-image restriction transition conjugated by the
identifications of the inverse images with the restrictions. -/
theorem componentDirectImageTransitionMap_eq
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    componentDirectImageTransitionMap a F φ =
      (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a m).pushforward.map
        ((componentInverseImageRestrictIso (C := C) m).hom.app F ≫
          ((situation C).restrictTransition φ).app F ≫
            ((situation C).transitionMorphism φ).pushforward.map
              ((componentInverseImageRestrictIso (C := C) n).inv.app F)) ≫
      (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
          (situation C) D K a φ).hom.app
        ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F) := by
  rw [show componentDirectImageTransitionMap a F φ =
      (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a m).pushforward.map
        ((((situation C).transitionMorphism φ).adj.homEquiv _ _)
          (((situation C).transitionMorphism φ).inverseImage.map
              ((componentInverseImageRestrictIso (C := C) m).hom.app F) ≫
            ((situation C).fiberTransition φ).app F ≫
              (componentInverseImageRestrictIso (C := C) n).inv.app F)) ≫
      (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
          (situation C) D K a φ).hom.app
        ((SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.obj F)
    from rfl]
  congr 1
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left, SimplicialSiteSituation.fiberTransition_adj,
    Category.assoc]

/-- **The cone law of Stacks 0D70, reduced.** A leg of the fork followed by a transition of the
direct images of the components is again a leg exactly when the corresponding law holds for the
legs read through the identifications of the inverse images with the restrictions. Both of those
identifications, and the adjunction of the simplicial transition morphism, have cancelled; what
remains depends on the adjunctions of the component inclusions only through the units of the
transported adjunctions `restrict k ⊣ g_{k,*}`. -/
theorem coneLaw_iff_restrictForm (F : Sheaf (situation C).totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (totalComponentUnitMap a F m ≫ componentDirectImageTransitionMap a F φ =
        totalComponentUnitMap a F n) ↔
      (MorphismOfTopoi.forkLegOfRestriction (totalMorphismOfTopoi a)
              (SimplicialSiteSituation.componentMorphism (situation C) m)
              (SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a m).pushforward
              (componentInclusionCompPushforwardIso a m)
              (componentInverseImageRestrictIso (C := C) m)
              (SimplicialSiteSituation.componentMorphism (situation C) m).adj F ≫
            (SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a m).pushforward.map
                (((situation C).restrictTransition φ).app F) ≫
              (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
                  (situation C) D K a φ).hom.app (((situation C).restrict n).obj F) =
          MorphismOfTopoi.forkLegOfRestriction (totalMorphismOfTopoi a)
            (SimplicialSiteSituation.componentMorphism (situation C) n)
            (SimplicialSiteSituation.Augmentation.componentAugmentation
              (situation C) D K a n).pushforward
            (componentInclusionCompPushforwardIso a n)
            (componentInverseImageRestrictIso (C := C) n)
            (SimplicialSiteSituation.componentMorphism (situation C) n).adj F) := by
  rw [totalComponentUnitMap_eq_forkLeg a m F, totalComponentUnitMap_eq_forkLeg a n F,
    componentDirectImageTransitionMap_eq a F φ]
  exact MorphismOfTopoi.forkLaw_iff (totalMorphismOfTopoi a)
    (SimplicialSiteSituation.componentMorphism (situation C) m)
    (SimplicialSiteSituation.componentMorphism (situation C) n)
    ((situation C).transitionMorphism φ)
    (SimplicialSiteSituation.Augmentation.componentAugmentation
      (situation C) D K a m).pushforward
    (SimplicialSiteSituation.Augmentation.componentAugmentation
      (situation C) D K a n).pushforward
    (componentInclusionCompPushforwardIso a m) (componentInclusionCompPushforwardIso a n)
    (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ)
    (componentInverseImageRestrictIso (C := C) m) (componentInverseImageRestrictIso (C := C) n)
    ((situation C).restrictTransition φ)
    (SimplicialSiteSituation.componentMorphism (situation C) m).adj
    (SimplicialSiteSituation.componentMorphism (situation C) n).adj F

/-- **The cone law of Stacks 0D70, reduced to two named obligations.** Given a comparison `θ` of
the direct image along the component inclusion of degree `m` composed with the simplicial
transition with the direct image along the component inclusion of degree `n`, satisfying the
compatibility `h1` with the two augmentation comparisons and the unit law `h2` in the total
topos, the cone law holds. Neither obligation is discharged here, and `θ` is not constructed. -/
theorem coneLaw_of_comparison (F : Sheaf (situation C).totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n)
    (θ : ((situation C).transitionMorphism φ).pushforward ⋙
        (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward ⟶
      (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward)
    (h1 : (componentInclusionCompPushforwardIso a m).hom.app
            (((situation C).transitionMorphism φ).pushforward.obj
              (((situation C).restrict n).obj F)) ≫
          (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
            (situation C) D K a φ).hom.app (((situation C).restrict n).obj F) =
        (totalMorphismOfTopoi a).pushforward.map (θ.app (((situation C).restrict n).obj F)) ≫
          (componentInclusionCompPushforwardIso a n).hom.app (((situation C).restrict n).obj F))
    (h2 : ((SimplicialSiteSituation.componentMorphism (situation C) m).adj.unit.app F ≫
          (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward.map
            ((componentInverseImageRestrictIso (C := C) m).hom.app F)) ≫
          (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward.map
              (((situation C).restrictTransition φ).app F) ≫
            θ.app (((situation C).restrict n).obj F) =
        (SimplicialSiteSituation.componentMorphism (situation C) n).adj.unit.app F ≫
          (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward.map
            ((componentInverseImageRestrictIso (C := C) n).hom.app F)) :
    totalComponentUnitMap a F m ≫ componentDirectImageTransitionMap a F φ =
      totalComponentUnitMap a F n :=
  (coneLaw_iff_restrictForm a F φ).mpr
    (MorphismOfTopoi.forkLaw_of_comparison (totalMorphismOfTopoi a)
      (SimplicialSiteSituation.componentMorphism (situation C) m)
      (SimplicialSiteSituation.componentMorphism (situation C) n)
      ((situation C).transitionMorphism φ)
      (SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a m).pushforward
      (SimplicialSiteSituation.Augmentation.componentAugmentation
        (situation C) D K a n).pushforward
      (componentInclusionCompPushforwardIso a m) (componentInclusionCompPushforwardIso a n)
      (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ)
      (componentInverseImageRestrictIso (C := C) m) (componentInverseImageRestrictIso (C := C) n)
      ((situation C).restrictTransition φ)
      (SimplicialSiteSituation.componentMorphism (situation C) m).adj
      (SimplicialSiteSituation.componentMorphism (situation C) n).adj F θ h1 h2)

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end

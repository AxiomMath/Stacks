module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkCounit

/-!
# The cone law of the total augmentation, reduced to one comparison of inverse images

The fork of the total augmentation of a cocontinuous simplicial site has, in each simplicial
degree, a leg from the total direct image to the direct image of that component, and the cone
law asserts that a leg followed by a transition of those direct images is again a leg. This
file carries that law across the three adjunctions of the component augmentations in a way
that leaves no counit and no unit behind: what remains is a single equation between natural
transformations of the *inverse* images, in which the three comparisons of direct images occur
only through the transformations conjugate to them and the transition of the simplicial site
occurs only through its inverse-image form.

Two steps do the work. The first is a bare naturality argument with no adjunction in it: given
any morphism `r` from the direct image along the inclusion of the target degree to the direct
image along the composite of the simplicial transition with the inclusion of the source degree,
compatible with the unit of the source degree, a leg followed by a transition is again a leg as
soon as `r` is compatible with the two augmentation comparisons. The second produces that
compatibility from the inverse-image equation, by reading the comparison `r` as the
transformation conjugate to the inverse-image transition and then composing conjugates: the
whiskerings of the conjugates are the conjugates of the whiskerings, so the three comparisons
and the transition combine into a single conjugate, and conjugation is a bijection.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentRestrictAdj`: the adjunction
  between restriction to a simplicial component and the direct image along the inclusion of
  that component. The inclusion of a component is both continuous and cocontinuous, so this is
  Mathlib's `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, and it is the adjunction whose
  unit the legs of the fork are built from once the inverse image has been identified with
  restriction.

## Main results

* `MorphismOfTopoi.forkLaw_of_directImageTransition`: a leg followed by a transition is again a
  leg, given a comparison of the two direct images along the component inclusions which is
  compatible with the unit of the source degree and with the two augmentation comparisons.
* `MorphismOfTopoi.directImageTransition_of_inverseImage`: that compatibility, for the
  comparison conjugate to a transformation of the inverse images, follows from the corresponding
  equation between the conjugates of the three comparisons of direct images.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.componentRestrictAdj_unit`: the unit
  of that adjunction is the unit of the chosen topos adjunction of the component inclusion,
  followed by the direct image of the identification of the inverse image with restriction.
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_of_inverseImageCompatibility`:
  the cone law of Stacks 0D70 (3) holds as soon as the conjugate of the comparison of the
  component augmentations along a simplicial transition, followed by the inverse image of the
  conjugate of the comparison in the source degree and by the inverse-image transition of the
  simplicial site, is the conjugate of the comparison in the target degree.

## Implementation notes

The comparison of a direct image with a composite of direct images runs between two right
adjoints of two left adjoints between the same pair of topoi, so each is the image of a unique
transformation of those left adjoints under Mathlib's `CategoryTheory.conjugateEquiv`. The
composition rule `CategoryTheory.conjugateEquiv_comp` reverses the order of composition and
asks that the adjunction in the middle be literally the same on both sides, which for the two
different bracketings of a threefold composite of adjunctions it is not: the two composite
adjunctions have the same left and right adjoints but units that differ by the functoriality of
one of them. They are nevertheless equal, by Mathlib's `CategoryTheory.Adjunction.ext`, which
needs only that the units agree.

The legs of the fork are built from the unit of the topos adjunction of the component inclusion,
followed by the direct image of the identification of its inverse image with restriction to the
component. That composite is the unit of the adjunction between restriction and the direct
image, because the identification is the comparison of two left adjoints of the same functor and
such a comparison transports one unit to the other.

The first step below mentions no adjunction at all; it is naturality of the augmentation
comparison of the source degree against the transition, followed by the compatibility of the
comparison `r` with the unit. That is why the comparison `r` is a hypothesis rather than a
construction: the only property of it used is that one compatibility, and in the application it
is the transformation conjugate to the inverse-image transition, for which the compatibility is
Mathlib's `CategoryTheory.unit_conjugateEquiv` together with
`CategoryTheory.SimplicialSiteSituation.fiberTransition_adj`.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u'' v₃ u₃

namespace CategoryTheory

namespace Adjunction

/-- Composition of adjunctions is associative. The two bracketings have the same left and right
adjoints, and their units differ only by the functoriality of the outer right adjoint. -/
theorem comp_assoc {T : Type u} [Category.{v} T] {Dd : Type u'} [Category.{v'} Dd]
    {Cm : Type u''} [Category.{v''} Cm] {Cn : Type u₃} [Category.{v₃} Cn]
    {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As) {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} (adjm : Rm ⊣ Gm)
    {Rf : Cm ⥤ Cn} {Gf : Cn ⥤ Cm} (adjf : Rf ⊣ Gf) :
    adjA.comp (adjm.comp adjf) = (adjA.comp adjm).comp adjf := by
  refine Adjunction.ext (NatTrans.ext (funext fun X => ?_))
  simp [Adjunction.comp]

end Adjunction

end CategoryTheory

namespace MorphismOfTopoi

variable {T : Type u} [Category.{v} T] {Dd : Type u'} [Category.{v'} Dd]
  {Cm : Type u''} [Category.{v''} Cm] {Cn : Type u₃} [Category.{v₃} Cn]

/-- **A leg followed by a transition is again a leg, given a comparison of the direct images
along the component inclusions in the direction of the transition.** The hypothesis `h2` says
that the comparison `r` carries the unit of the target degree to the unit of the source degree
transported along the transition `w`, and `hH` says that `r` is compatible with the two
comparisons of the augmentations. No adjunction occurs: the proof is naturality of the
comparison in the source degree against `w`, and then `h2` and `hH`. -/
theorem forkLaw_of_directImageTransition
    {As : T ⥤ Dd} {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} {Rn : T ⥤ Cn} {Gn : Cn ⥤ T}
    {Gf : Cn ⥤ Cm} {Bms : Cm ⥤ Dd} {Bns : Cn ⥤ Dd}
    (pm : Gm ⋙ As ≅ Bms) (pn : Gn ⋙ As ⟶ Bns) (t : Gf ⋙ Bms ⟶ Bns)
    (r : Gn ⟶ Gf ⋙ Gm) (F : T)
    (ηm : F ⟶ Gm.obj (Rm.obj F)) (ηn : F ⟶ Gn.obj (Rn.obj F))
    (w : Rm.obj F ⟶ Gf.obj (Rn.obj F))
    (h2 : ηm ≫ Gm.map w = ηn ≫ r.app (Rn.obj F))
    (hH : As.map (r.app (Rn.obj F)) ≫ pm.hom.app (Gf.obj (Rn.obj F)) ≫ t.app (Rn.obj F) =
      pn.app (Rn.obj F)) :
    As.map ηm ≫ pm.hom.app (Rm.obj F) ≫ Bms.map w ≫ t.app (Rn.obj F) =
      As.map ηn ≫ pn.app (Rn.obj F) := by
  have hnat := pm.hom.naturality w
  simp only [Functor.comp_map] at hnat
  rw [← hH, ← reassoc_of% hnat, ← As.map_comp_assoc, h2, As.map_comp_assoc]

/-- **The compatibility of the conjugate comparison with the two augmentation comparisons, from
one equation between inverse images.** The comparison of direct images conjugate to a
transformation `ν` of the inverse images satisfies the hypothesis `hH` of
`MorphismOfTopoi.forkLaw_of_directImageTransition` exactly when the conjugate of the transition
comparison, followed by the inverse image of the conjugate of the comparison in the source
degree and by `ν`, is the conjugate of the comparison in the target degree. Both whiskerings on
the left are conjugates of whiskerings, so the left-hand side is a single conjugate, and
conjugation is a bijection. -/
theorem directImageTransition_of_inverseImage
    {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {Rm : T ⥤ Cm} {Gm : Cm ⥤ T} (adjm : Rm ⊣ Gm)
    {Rn : T ⥤ Cn} {Gn : Cn ⥤ T} (adjn : Rn ⊣ Gn)
    {Rf : Cm ⥤ Cn} {Gf : Cn ⥤ Cm} (adjf : Rf ⊣ Gf)
    {Bmi : Dd ⥤ Cm} {Bms : Cm ⥤ Dd} (adjBm : Bmi ⊣ Bms)
    {Bni : Dd ⥤ Cn} {Bns : Cn ⥤ Dd} (adjBn : Bni ⊣ Bns)
    (pm : Gm ⋙ As ≅ Bms) (pn : Gn ⋙ As ≅ Bns) (t : Gf ⋙ Bms ≅ Bns)
    (ν : Rm ⋙ Rf ⟶ Rn)
    (hstar : (conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom ≫
        Functor.whiskerRight ((conjugateEquiv (adjA.comp adjm) adjBm).symm pm.hom) Rf ≫
          Functor.whiskerLeft Ai ν =
      (conjugateEquiv (adjA.comp adjn) adjBn).symm pn.hom) :
    Functor.whiskerRight (conjugateEquiv adjn (adjm.comp adjf) ν) As ≫
        Functor.whiskerLeft Gf pm.hom ≫ t.hom = pn.hom := by
  have e1 : conjugateEquiv (adjA.comp adjn) (adjA.comp (adjm.comp adjf))
        (Functor.whiskerLeft Ai ν) =
      Functor.whiskerRight (conjugateEquiv adjn (adjm.comp adjf) ν) As :=
    conjugateEquiv_whiskerLeft adjn (adjm.comp adjf) adjA ν
  have e2 : conjugateEquiv (adjA.comp (adjm.comp adjf)) (adjBm.comp adjf)
        (Functor.whiskerRight ((conjugateEquiv (adjA.comp adjm) adjBm).symm pm.hom) Rf) =
      Functor.whiskerLeft Gf pm.hom := by
    rw [Adjunction.comp_assoc adjA adjm adjf, conjugateEquiv_whiskerRight,
      Equiv.apply_symm_apply]
  have e3 : conjugateEquiv (adjBm.comp adjf) adjBn
      ((conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom) = t.hom :=
    Equiv.apply_symm_apply _ _
  have e4 : conjugateEquiv (adjA.comp adjn) adjBn
      ((conjugateEquiv (adjA.comp adjn) adjBn).symm pn.hom) = pn.hom :=
    Equiv.apply_symm_apply _ _
  rw [← e1, ← e2, ← e3, ← e4, ← Category.assoc,
    conjugateEquiv_comp (adjA.comp adjn) (adjA.comp (adjm.comp adjf)) (adjBm.comp adjf),
    conjugateEquiv_comp (adjA.comp adjn) (adjBm.comp adjf) adjBn]
  exact congrArg _ hstar

end MorphismOfTopoi

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-- The adjunction between restriction to the component in simplicial degree `k` and the direct
image along the inclusion of that component. The inclusion is both continuous and cocontinuous,
so this is Mathlib's adjunction for such a functor; its right adjoint is the direct image of the
chosen morphism of topoi of the inclusion on the nose. -/
def componentRestrictAdj (k : SimplexCategory) :
    (situation C).restrict k ⊣
      (SimplicialSiteSituation.componentMorphism (situation C) k).pushforward :=
  (SimplicialSiteSituation.inclusion (situation C) k).sheafAdjunctionCocontinuous (Type u)
    ((situation C).componentTopology k) (situation C).totalTopology

/-- The unit of `componentRestrictAdj` is the unit of the chosen topos adjunction of the
component inclusion, followed by the direct image of the identification of the inverse image
with restriction. That identification is the comparison of two left adjoints of the direct
image, so it transports one unit to the other. -/
theorem componentRestrictAdj_unit (k : SimplexCategory)
    (F : Sheaf (situation C).totalTopology (Type u)) :
    (SimplicialSiteSituation.componentMorphism (situation C) k).adj.unit.app F ≫
        (SimplicialSiteSituation.componentMorphism (situation C) k).pushforward.map
          ((componentInverseImageRestrictIso (C := C) k).hom.app F) =
      (componentRestrictAdj k).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

variable (a : C.Augmentation D K)

/-- **The cone law of Stacks 0D70 (3), from one equation between inverse images.** A leg of the
fork of the total augmentation, followed by the transition of the direct images of the
components attached to a simplex map, is again a leg, provided the conjugate of the comparison
of the component augmentations along that simplex map, followed by the inverse image of the
conjugate of the comparison of the total augmentation with the augmentation of the source
degree and then by the inverse-image transition of the simplicial site, is the conjugate of the
comparison in the target degree. Each of the three comparisons of direct images enters only
through its conjugate, and the only transition that appears is the inverse-image one. -/
theorem coneLaw_of_inverseImageCompatibility
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n)
    (hstar : (conjugateEquiv
            ((SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a m).adj.comp
              ((situation C).transitionMorphism φ).adj)
            (SimplicialSiteSituation.Augmentation.componentAugmentation
              (situation C) D K a n).adj).symm
          (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
            (situation C) D K a φ).hom ≫
        Functor.whiskerRight
            ((conjugateEquiv ((totalMorphismOfTopoi a).adj.comp (componentRestrictAdj m))
                (SimplicialSiteSituation.Augmentation.componentAugmentation
                  (situation C) D K a m).adj).symm
              (componentInclusionCompPushforwardIso a m).hom)
            ((situation C).transitionMorphism φ).inverseImage ≫
          Functor.whiskerLeft (totalMorphismOfTopoi a).inverseImage
            ((situation C).fiberTransition φ) =
      (conjugateEquiv ((totalMorphismOfTopoi a).adj.comp (componentRestrictAdj n))
          (SimplicialSiteSituation.Augmentation.componentAugmentation
            (situation C) D K a n).adj).symm
        (componentInclusionCompPushforwardIso a n).hom) :
    totalComponentUnitMap a F m ≫ componentDirectImageTransitionMap a F φ =
      totalComponentUnitMap a F n := by
  refine (coneLaw_iff_restrictForm a F φ).mpr ?_
  have key : ∀ k : SimplexCategory, MorphismOfTopoi.forkLegOfRestriction (totalMorphismOfTopoi a)
        (SimplicialSiteSituation.componentMorphism (situation C) k)
        (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a k).pushforward
        (componentInclusionCompPushforwardIso a k)
        (componentInverseImageRestrictIso (C := C) k)
        (SimplicialSiteSituation.componentMorphism (situation C) k).adj F =
      (totalMorphismOfTopoi a).pushforward.map ((componentRestrictAdj k).unit.app F) ≫
        (componentInclusionCompPushforwardIso a k).hom.app
          (((situation C).restrict k).obj F) := fun k => by
    rw [← componentRestrictAdj_unit k F]; rfl
  rw [key m, key n]
  refine MorphismOfTopoi.forkLaw_of_directImageTransition
    (componentInclusionCompPushforwardIso a m)
    (componentInclusionCompPushforwardIso a n).hom
    (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ).hom
    (conjugateEquiv (componentRestrictAdj n)
      ((componentRestrictAdj m).comp ((situation C).transitionMorphism φ).adj)
      ((situation C).fiberTransition φ)) F ((componentRestrictAdj m).unit.app F)
    ((componentRestrictAdj n).unit.app F) (((situation C).restrictTransition φ).app F) ?_ ?_
  · rw [← SimplicialSiteSituation.fiberTransition_adj (situation C) φ F,
      Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← Adjunction.comp_unit_app]
    exact (unit_conjugateEquiv (componentRestrictAdj n)
      ((componentRestrictAdj m).comp ((situation C).transitionMorphism φ).adj)
      ((situation C).fiberTransition φ) F).symm
  · exact NatTrans.congr_app
      (MorphismOfTopoi.directImageTransition_of_inverseImage (totalMorphismOfTopoi a).adj
        (componentRestrictAdj m) (componentRestrictAdj n)
        ((situation C).transitionMorphism φ).adj
        (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a m).adj
        (SimplicialSiteSituation.Augmentation.componentAugmentation
          (situation C) D K a n).adj
        (componentInclusionCompPushforwardIso a m) (componentInclusionCompPushforwardIso a n)
        (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ)
        ((situation C).fiberTransition φ) hstar) (((situation C).restrict n).obj F)

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end

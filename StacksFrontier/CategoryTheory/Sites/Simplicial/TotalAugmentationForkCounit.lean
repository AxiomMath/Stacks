module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationForkReduction

/-!
# The cone law of the total augmentation as a condition on one counit

The fork of the total augmentation has, in each simplicial degree, a leg from the total direct
image to the direct image of that component, and the cone law asserts that a leg followed by a
transition of those direct images is again a leg. This file transposes that law across the
adjunction of the component augmentation of the target degree. Both sides become maps of
inverse images, the three comparisons of direct images enter only through the natural
transformations conjugate to them, and what remains is a single equation between two
restrictions of the counit of the total adjunction.

The same transposition settles the route through a comparison of the direct images along the
two component inclusions, which is how
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_of_comparison` derives the law:
the unit law asked of such a comparison is equivalent to the inverse-image transition of the
simplicial site being a split epimorphism, so that route asks for strictly more than the law it
proves.

## Main results

* `MorphismOfTopoi.forkLeg_transpose`: the transpose of a fork leg is the counit of the total
  adjunction, read through the comparison of left adjoints conjugate to the comparison of
  direct images.
* `MorphismOfTopoi.forkLawComparison_transpose`: the transpose of a map which factors through
  the comparison of direct images along a transition.
* `MorphismOfTopoi.forkLaw_iff_counitForm` and
  `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_iff_counitForm`: the cone law
  holds if and only if one equation between restrictions of the counit does.
* `MorphismOfTopoi.forkLaw_unitLaw_iff`,
  `MorphismOfTopoi.isSplitEpi_of_forkLaw_unitLaw` and
  `CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_unitLaw_forces_isSplitEpi`:
  the unit law of the comparison route is a splitting condition on the inverse-image
  transition.

## Implementation notes

Every comparison of direct images here is a map between two right adjoints of two left
adjoints between the same pair of categories, so each is the image of a unique map of those
left adjoints under Mathlib's `CategoryTheory.conjugateEquiv`. The transposition is then
bookkeeping with `CategoryTheory.conjugateEquiv_counit` and
`CategoryTheory.unit_conjugateEquiv`, and the triangle identity is what removes the units: no
coherence of the comparisons themselves is used, and none is constructed.

The comparison of direct images along the two component inclusions runs in the direction
opposite to the one the inverse-image transition induces, which is why it is not the conjugate
of that transition and why the route through it is not the transposition carried out here.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u'' v₃ u₃

namespace MorphismOfTopoi

variable {T : Type u} [Category.{v} T] {Dd : Type u'} [Category.{v'} Dd]
  {Cm : Type u''} [Category.{v''} Cm] {Cn : Type u₃} [Category.{v₃} Cn]

/-- Transposing a map into a direct image that factors through a comparison `t` of direct images
gives the conjugate of `t` followed by the transposes of the factors. -/
private theorem transpose_comp_comparison {Bmi : Dd ⥤ Cm} {Bms : Cm ⥤ Dd} (adjBm : Bmi ⊣ Bms)
    {Bni : Dd ⥤ Cn} {Bns : Cn ⥤ Dd} (adjBn : Bni ⊣ Bns)
    {fi : Cm ⥤ Cn} {fs : Cn ⥤ Cm} (adjf : fi ⊣ fs)
    (t : fs ⋙ Bms ≅ Bns) {X : Dd} {Ym : Cm} {Yn : Cn}
    (x : X ⟶ Bms.obj Ym) (w : Ym ⟶ fs.obj Yn) :
    (adjBn.homEquiv X Yn).symm (x ≫ Bms.map w ≫ t.hom.app Yn) =
      ((conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom).app X ≫
        fi.map ((adjBm.homEquiv X Ym).symm x) ≫ (adjf.homEquiv Ym Yn).symm w := by
  set s := (conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom
  have hcc := conjugateEquiv_counit_symm (adjBm.comp adjf) adjBn t.hom Yn
  have hnatw : Bni.map (Bms.map w) ≫ s.app ((fs ⋙ Bms).obj Yn) =
      s.app (Bms.obj Ym) ≫ fi.map (Bmi.map (Bms.map w)) :=
    s.naturality (Bms.map w)
  have hnatx : Bni.map x ≫ s.app (Bms.obj Ym) = s.app X ≫ fi.map (Bmi.map x) :=
    s.naturality x
  have hcn : Bmi.map (Bms.map w) ≫ adjBm.counit.app (fs.obj Yn) =
      adjBm.counit.app Ym ≫ w := adjBm.counit.naturality w
  have hcnf : fi.map (Bmi.map (Bms.map w)) ≫ fi.map (adjBm.counit.app (fs.obj Yn)) =
      fi.map (adjBm.counit.app Ym) ≫ fi.map w := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hcn]
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply,
    Adjunction.homEquiv_symm_apply, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, hcc,
    Adjunction.comp_counit_app adjBm adjf Yn,
    ← Category.assoc (Bni.map (Bms.map w)), hnatw, Category.assoc,
    reassoc_of% hnatx, reassoc_of% hcnf]
  simp

/-- The transpose of a fork leg is the counit of the total adjunction, read through the
comparison of left adjoints conjugate to `p`. A leg is built from the unit of `g` and the
comparison `p` of direct images; transposing it across the adjunction of `B` turns both into
the counit of `A`, because the two units cancel against the triangle identity. -/
theorem forkLeg_transpose {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {gi : T ⥤ Cm} {gs : Cm ⥤ T} (adjg : gi ⊣ gs)
    {Bi : Dd ⥤ Cm} {Bs : Cm ⥤ Dd} (adjB : Bi ⊣ Bs)
    (p : gs ⋙ As ≅ Bs) (F : T) :
    (adjB.homEquiv (As.obj F) (gi.obj F)).symm
        (As.map (adjg.unit.app F) ≫ p.hom.app (gi.obj F)) =
      ((conjugateEquiv (adjA.comp adjg) adjB).symm p.hom).app (As.obj F) ≫
        gi.map (adjA.counit.app F) := by
  simpa [Adjunction.homEquiv_counit] using
    transpose_comp_comparison adjA adjB adjg p (𝟙 (As.obj F)) (adjg.unit.app F)

/-- The transpose of a map into the direct image of the target degree which factors through the
comparison `t`: the comparison contributes its conjugate on the inverse images, and the factor
`w` contributes its own transpose. -/
theorem forkLawComparison_transpose {Bmi : Dd ⥤ Cm} {Bms : Cm ⥤ Dd} (adjBm : Bmi ⊣ Bms)
    {Bni : Dd ⥤ Cn} {Bns : Cn ⥤ Dd} (adjBn : Bni ⊣ Bns)
    {fi : Cm ⥤ Cn} {fs : Cn ⥤ Cm} (adjf : fi ⊣ fs)
    (t : fs ⋙ Bms ≅ Bns) {X : Dd} {Ym : Cm} {Yn : Cn}
    (x : X ⟶ Bms.obj Ym) (w : Ym ⟶ fs.obj Yn) :
    (adjBn.homEquiv X Yn).symm (x ≫ Bms.map w ≫ t.hom.app Yn) =
      ((conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom).app X ≫
        fi.map ((adjBm.homEquiv X Ym).symm x) ≫ (adjf.homEquiv Ym Yn).symm w :=
  transpose_comp_comparison adjBm adjBn adjf t x w

/-- **The cone law, reduced to an equation between restrictions of one counit.** The law that a
fork leg followed by a comparison of direct images is again a leg holds if and only if the
counit of the total adjunction, restricted to the source degree and transported along the
factor `w`, agrees with its restriction to the target degree. Both sides live on the inverse
images, the three comparisons of direct images appear only through their conjugates, and no
comparison of the direct images along the two component inclusions occurs at all. -/
theorem forkLaw_iff_counitForm {Ai : Dd ⥤ T} {As : T ⥤ Dd} (adjA : Ai ⊣ As)
    {gmi : T ⥤ Cm} {gms : Cm ⥤ T} (adjm : gmi ⊣ gms)
    {gni : T ⥤ Cn} {gns : Cn ⥤ T} (adjn : gni ⊣ gns)
    {Bmi : Dd ⥤ Cm} {Bms : Cm ⥤ Dd} (adjBm : Bmi ⊣ Bms)
    {Bni : Dd ⥤ Cn} {Bns : Cn ⥤ Dd} (adjBn : Bni ⊣ Bns)
    {fi : Cm ⥤ Cn} {fs : Cn ⥤ Cm} (adjf : fi ⊣ fs)
    (pm : gms ⋙ As ≅ Bms) (pn : gns ⋙ As ≅ Bns) (t : fs ⋙ Bms ≅ Bns) (F : T)
    (w : gmi.obj F ⟶ fs.obj (gni.obj F)) :
    ((As.map (adjm.unit.app F) ≫ pm.hom.app (gmi.obj F)) ≫
          Bms.map w ≫ t.hom.app (gni.obj F) =
        As.map (adjn.unit.app F) ≫ pn.hom.app (gni.obj F)) ↔
      (((conjugateEquiv (adjBm.comp adjf) adjBn).symm t.hom).app (As.obj F) ≫
            fi.map (((conjugateEquiv (adjA.comp adjm) adjBm).symm pm.hom).app (As.obj F) ≫
              gmi.map (adjA.counit.app F)) ≫
            (adjf.homEquiv (gmi.obj F) (gni.obj F)).symm w =
        ((conjugateEquiv (adjA.comp adjn) adjBn).symm pn.hom).app (As.obj F) ≫
          gni.map (adjA.counit.app F)) := by
  rw [← Equiv.apply_eq_iff_eq (adjBn.homEquiv (As.obj F) (gni.obj F)).symm,
    forkLawComparison_transpose adjBm adjBn adjf t _ w,
    forkLeg_transpose adjA adjm adjBm pm F, forkLeg_transpose adjA adjn adjBn pn F]

/-- **The unit law of the comparison route is a splitting condition.** Every natural
transformation of the direct images is the conjugate of a unique transformation of the inverse
images, and the unit law asked of such a comparison says exactly that the latter is a section of
the inverse-image transition. -/
theorem forkLaw_unitLaw_iff {Rm : T ⥤ Cm} {gms : Cm ⥤ T} (adjm : Rm ⊣ gms)
    {Rn : T ⥤ Cn} {gns : Cn ⥤ T} (adjn : Rn ⊣ gns)
    {fi : Cm ⥤ Cn} {fs : Cn ⥤ Cm} (adjf : fi ⊣ fs)
    (ft : Rm ⋙ fi ⟶ Rn) (θ : fs ⋙ gms ⟶ gns) (F : T) :
    (adjm.unit.app F ≫
        gms.map (adjf.unit.app (Rm.obj F) ≫ fs.map (ft.app F)) ≫ θ.app (Rn.obj F) =
      adjn.unit.app F) ↔
      ((conjugateEquiv (adjm.comp adjf) adjn).symm θ).app F ≫ ft.app F = 𝟙 (Rn.obj F) := by
  set α := (conjugateEquiv (adjm.comp adjf) adjn).symm θ
  have hu := unit_conjugateEquiv_symm (adjm.comp adjf) adjn θ F
  have hnat := θ.naturality (ft.app F)
  simp only [Functor.comp_map] at hnat
  have key : adjm.unit.app F ≫
      gms.map (adjf.unit.app (Rm.obj F) ≫ fs.map (ft.app F)) ≫ θ.app (Rn.obj F) =
      adjn.unit.app F ≫ gns.map (α.app F ≫ ft.app F) :=
    calc adjm.unit.app F ≫
          gms.map (adjf.unit.app (Rm.obj F) ≫ fs.map (ft.app F)) ≫ θ.app (Rn.obj F)
        = (adjm.unit.app F ≫ gms.map (adjf.unit.app (Rm.obj F))) ≫
            (gms.map (fs.map (ft.app F)) ≫ θ.app (Rn.obj F)) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = (adjm.comp adjf).unit.app F ≫ θ.app ((Rm ⋙ fi).obj F) ≫ gns.map (ft.app F) := by
          rw [← Adjunction.comp_unit_app adjm adjf F, hnat]
      _ = (adjn.unit.app F ≫ gns.map (α.app F)) ≫ gns.map (ft.app F) := by
          rw [← Category.assoc, hu]
      _ = adjn.unit.app F ≫ gns.map (α.app F ≫ ft.app F) := by
          rw [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [key]
  refine ⟨fun h => (adjn.homEquiv F (Rn.obj F)).injective ?_, fun h => ?_⟩
  · rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h]
    simp
  · rw [h]
    simp

/-- A comparison satisfying the unit law exists only if the inverse-image transition is a split
epimorphism. -/
theorem isSplitEpi_of_forkLaw_unitLaw {Rm : T ⥤ Cm} {gms : Cm ⥤ T} (adjm : Rm ⊣ gms)
    {Rn : T ⥤ Cn} {gns : Cn ⥤ T} (adjn : Rn ⊣ gns)
    {fi : Cm ⥤ Cn} {fs : Cn ⥤ Cm} (adjf : fi ⊣ fs)
    (ft : Rm ⋙ fi ⟶ Rn) (θ : fs ⋙ gms ⟶ gns) (F : T)
    (h : adjm.unit.app F ≫
        gms.map (adjf.unit.app (Rm.obj F) ≫ fs.map (ft.app F)) ≫ θ.app (Rn.obj F) =
      adjn.unit.app F) :
    IsSplitEpi (ft.app F) :=
  IsSplitEpi.mk' ⟨_, (forkLaw_unitLaw_iff adjm adjn adjf ft θ F).mp h⟩

end MorphismOfTopoi

namespace CategoryTheory

namespace CocontinuousSimplicialSite

namespace Augmentation

variable {C : CocontinuousSimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}

/-- The direct-image restriction transition is the transpose of the inverse-image one. -/
theorem restrictTransition_app_eq (F : Sheaf (situation C).totalTopology (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation C).restrictTransition φ).app F =
      ((situation C).transitionMorphism φ).adj.unit.app (((situation C).restrict m).obj F) ≫
        ((situation C).transitionMorphism φ).pushforward.map
          (((situation C).fiberTransition φ).app F) := by
  rw [← SimplicialSiteSituation.fiberTransition_adj (situation C) φ F,
    Adjunction.homEquiv_unit]

/-- **The unit law of Stacks 0D70's comparison route is a splitting condition.** If a comparison
of the direct images along the component inclusions satisfies the unit law of
`CategoryTheory.CocontinuousSimplicialSite.Augmentation.coneLaw_of_comparison`, then the
inverse-image transition of the simplicial site is a split epimorphism at that sheaf. Nothing in
the data of a cocontinuous simplicial site supplies such a splitting, and the cone law itself
does not assert one: the route therefore asks for strictly more than the law it is used to
prove. The statement mentions no augmentation, so the condition is independent of the
augmentation entirely. -/
theorem coneLaw_unitLaw_forces_isSplitEpi
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n)
    (θ : ((situation C).transitionMorphism φ).pushforward ⋙
        (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward ⟶
      (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward)
    (h2 : ((SimplicialSiteSituation.componentMorphism (situation C) m).adj.unit.app F ≫
          (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward.map
            ((componentInverseImageRestrictIso (C := C) m).hom.app F)) ≫
          (SimplicialSiteSituation.componentMorphism (situation C) m).pushforward.map
              (((situation C).restrictTransition φ).app F) ≫
            θ.app (((situation C).restrict n).obj F) =
        (SimplicialSiteSituation.componentMorphism (situation C) n).adj.unit.app F ≫
          (SimplicialSiteSituation.componentMorphism (situation C) n).pushforward.map
            ((componentInverseImageRestrictIso (C := C) n).hom.app F)) :
    IsSplitEpi (((situation C).fiberTransition φ).app F) := by
  refine MorphismOfTopoi.isSplitEpi_of_forkLaw_unitLaw
    ((SimplicialSiteSituation.componentMorphism (situation C) m).adj.ofNatIsoLeft
      (componentInverseImageRestrictIso (C := C) m))
    ((SimplicialSiteSituation.componentMorphism (situation C) n).adj.ofNatIsoLeft
      (componentInverseImageRestrictIso (C := C) n))
    ((situation C).transitionMorphism φ).adj ((situation C).fiberTransition φ) θ F ?_
  rwa [Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_unit,
    ← restrictTransition_app_eq (C := C) F φ, ← Category.assoc]

/-- **The cone law of Stacks 0D70, reduced to one equation between restrictions of one
counit.** The cone law holds if and only if the counit of the total augmentation's adjunction,
restricted to the component of the source degree and then transported along the inverse-image
transition, agrees with its restriction to the component of the target degree. Each of the
three comparisons of direct images enters only through its conjugate on the inverse images, and
no comparison of the direct images along the two component inclusions remains. -/
theorem coneLaw_iff_counitForm (a : C.Augmentation D K)
    (F : Sheaf (situation C).totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (totalComponentUnitMap a F m ≫ componentDirectImageTransitionMap a F φ =
        totalComponentUnitMap a F n) ↔
      (((conjugateEquiv
              ((SimplicialSiteSituation.Augmentation.componentAugmentation
                  (situation C) D K a m).adj.comp
                ((situation C).transitionMorphism φ).adj)
              (SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a n).adj).symm
            (SimplicialSiteSituation.Augmentation.transitionPushforwardIso
              (situation C) D K a φ).hom).app
            ((totalMorphismOfTopoi a).pushforward.obj F) ≫
          ((situation C).transitionMorphism φ).inverseImage.map
            (((conjugateEquiv
                  ((totalMorphismOfTopoi a).adj.comp
                    (SimplicialSiteSituation.componentMorphism (situation C) m).adj)
                  (SimplicialSiteSituation.Augmentation.componentAugmentation
                    (situation C) D K a m).adj).symm
                (componentInclusionCompPushforwardIso a m).hom).app
                ((totalMorphismOfTopoi a).pushforward.obj F) ≫
              (SimplicialSiteSituation.componentMorphism (situation C) m).inverseImage.map
                ((totalMorphismOfTopoi a).adj.counit.app F)) ≫
            (((situation C).transitionMorphism φ).adj.homEquiv _ _).symm
              ((componentInverseImageRestrictIso (C := C) m).hom.app F ≫
                ((situation C).restrictTransition φ).app F ≫
                  ((situation C).transitionMorphism φ).pushforward.map
                    ((componentInverseImageRestrictIso (C := C) n).inv.app F)) =
        ((conjugateEquiv
              ((totalMorphismOfTopoi a).adj.comp
                (SimplicialSiteSituation.componentMorphism (situation C) n).adj)
              (SimplicialSiteSituation.Augmentation.componentAugmentation
                (situation C) D K a n).adj).symm
            (componentInclusionCompPushforwardIso a n).hom).app
            ((totalMorphismOfTopoi a).pushforward.obj F) ≫
          (SimplicialSiteSituation.componentMorphism (situation C) n).inverseImage.map
            ((totalMorphismOfTopoi a).adj.counit.app F)) := by
  rw [componentDirectImageTransitionMap_eq a F φ]
  exact MorphismOfTopoi.forkLaw_iff_counitForm (totalMorphismOfTopoi a).adj
    (SimplicialSiteSituation.componentMorphism (situation C) m).adj
    (SimplicialSiteSituation.componentMorphism (situation C) n).adj
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation C) D K a m).adj
    (SimplicialSiteSituation.Augmentation.componentAugmentation (situation C) D K a n).adj
    ((situation C).transitionMorphism φ).adj
    (componentInclusionCompPushforwardIso a m) (componentInclusionCompPushforwardIso a n)
    (SimplicialSiteSituation.Augmentation.transitionPushforwardIso (situation C) D K a φ) F _

end Augmentation

end CocontinuousSimplicialSite

end CategoryTheory

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# The smooth locus and a change of base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site and `𝒳` an algebraic stack over `S`.
Construction A of Stacks 04X5 views `𝒳` as an algebraic stack over `S'`, with a 1-morphism to the
algebraic stack represented by `S/S'`; the two have the same objects. This file shows that the
smooth locus (Stacks 0DZR) of the structure morphism `𝒳 ⟶ S` and the smooth locus over `S'` of
`𝒳 ⟶ S/S'` cut out the same objects.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_spacesOverSmallerBaseFunctor_iff`: being an open
  immersion, for the structural morphism of the image of Stacks 04SG's forward functor, does not
  depend on the base.
* `AlgebraicGeometry.Stack.isOpenImmersion_changeBaseHom_iff`: the open-immersion condition of
  Stacks 04XB is unchanged by Construction A.
* `AlgebraicGeometry.Stack.OpenSubstack.changeBase` and
  `AlgebraicGeometry.Stack.OpenSubstack.ofChangeBase`: open substacks over `S` and over `S'`
  correspond, with the same property of objects.
* `AlgebraicGeometry.Stack.isSmooth_structureMorphism_iff_changeBase`: the structure morphism
  `𝒳 ⟶ S` is smooth exactly when `𝒳 ⟶ S/S'` is smooth over `S'`.
* `AlgebraicGeometry.Stack.IsSmoothLocus.property_eq_changeBase`: the two smooth loci have the
  same objects.

## Implementation notes

Smoothness of a 1-morphism into the stack of a scheme is read on a smooth surjective presentation
of the source by a scheme `U` over `S` (cancellation of smoothness along it): over `S` the
composite is the structure morphism of `(Sch/U)`, smooth exactly when `U ⟶ S` is, and over `S'`
the presentation pushed forward by Construction A composes to a 1-morphism of scheme stacks whose
morphism of the site is `U ⟶ S`, smooth exactly when that morphism of schemes is (Stacks 06FM for
representable source and target).

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace Space

section SmallerBase

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- Being an open immersion of presheaves respects isomorphisms: it is a base-change-stable
property of morphisms of presheaves. -/
theorem isOpenImmersion_respectsIso :
    MorphismProperty.RespectsIso (@Space.IsOpenImmersion B S hS) := by
  have h₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- **Being an open immersion is unchanged by the lower-shriek extension.** -/
theorem isOpenImmersion_relocalizeMap_iff {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y) :
    IsOpenImmersion B S hS ((OverShriek.relocalizePresheafFunctor h).map k) ↔
      IsOpenImmersion B W hW k :=
  ⟨presheaf_relocalizeMap_of B W S hW hS h
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) k,
    presheaf_relocalizeMap B W S hW hS h
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) k⟩

/-- **The structural morphism of a lower-shriek extension is an open immersion exactly when the
structural morphism over `W` is one.** -/
theorem isOpenImmersion_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsOpenImmersion B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsOpenImmersion B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  have _ := isOpenImmersion_respectsIso B S hS
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F,
    MorphismProperty.cancel_right_of_respectsIso (@Space.IsOpenImmersion B S hS)]
  exact isOpenImmersion_relocalizeMap_iff B W S hW hS h (toYonedaId B W hW F)

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **The structural morphism of an algebraic space over `W` is an open immersion over `S`
exactly when it is one over a larger base `S'`.** Both sides are the condition over `W`. -/
theorem isOpenImmersion_relocalizeToYoneda_comp_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsOpenImmersion B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      IsOpenImmersion B S hS (OverShriek.relocalizeToYoneda h F) :=
  (isOpenImmersion_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) F).trans
    (isOpenImmersion_relocalizeToYoneda_iff B W S hW hS h F).symm

/-- **Being an open immersion, for the structural morphism of the image of Stacks 04SG's forward
functor, does not depend on the base.** An algebraic space over `W`, viewed over `S` along `h`
and over `S'` along a factorization `h ≫ g`, has open immersion structural morphism over `S`
exactly when it has one over `S'`. -/
theorem isOpenImmersion_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    IsOpenImmersion B S' hS'
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      IsOpenImmersion B S hS
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  have _ := isOpenImmersion_respectsIso B S hS
  have _ := isOpenImmersion_respectsIso B S' hS'
  rw [← MorphismProperty.cancel_left_of_respectsIso (@Space.IsOpenImmersion B S hS)
      ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _,
    ← MorphismProperty.cancel_left_of_respectsIso (@Space.IsOpenImmersion B S' hS')
      ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _,
    relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩,
    relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩]
  exact isOpenImmersion_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g F

end SmallerBase

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The open-immersion condition of Stacks 04XB is unchanged by Construction A.** A 1-morphism
of categories fibred in groupoids over the big fppf site of `S` is an open immersion in the
relative sense of Stacks 04XB exactly when the 1-morphism over the big fppf site of `S'` produced
by Construction A is one. -/
theorem isOpenImmersion_changeBaseHom_iff
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    IsOpenImmersion B S' hS' (changeBaseHom B S S' hS hS' g f) ↔
      IsOpenImmersion B S hS f := by
  constructor
  · intro hbig U y hy F hF ⟨E⟩
    exact (Space.isOpenImmersion_spacesOverSmallerBaseFunctor_iff B U.left.1 S U.left.2 hS
      U.hom S' hS' g (U.hom ≫ g) rfl F hF).1 (hbig ((Over.map g).obj U) y
        (comp_changeBase_p_eq_map B S S' hS hS' g 𝒴.val U y hy) F hF
        ⟨TwoFibreProductOver.unrelocalizeFstEquivalenceOver_trans g hy f.hom.w E⟩)
  · intro hsmall U' y hy' F hF ⟨E'⟩
    obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
    rw [← hg, Over.mapComp_eq] at E'
    exact (Space.isOpenImmersion_spacesOverSmallerBaseFunctor_iff B U'.left.1 S U'.left.2
      hS h₀ S' hS' g U'.hom hg F hF).2
        (hsmall (Over.mk h₀) y hy F hF
          ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩)

/-! ### Open substacks across Construction A -/

/-- **An open substack over `S` is an open substack over `S'`.** The same strictly full
subcategory of `𝒳` is an open substack of `𝒳` viewed over `S'` by Construction A: algebraicity
transfers by Stacks 04X5 and the open immersion condition by
`AlgebraicGeometry.Stack.isOpenImmersion_changeBaseHom_iff`. -/
def OpenSubstack.changeBase {𝒳 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳) :
    OpenSubstack (changeBaseAlgebraicStack B S S' hS hS' g 𝒳) where
  property := W.property
  strictlyFull := W.strictlyFull
  isAlgebraic := (isAlgebraicStack_changeBase_iff B S S' hS hS' g
    (fullSubcategoryBased 𝒳 W.property)).2 W.isAlgebraic
  isOpenImmersion :=
    ⟨(isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
        (fullSubcategoryBasedInclusion 𝒳 W.property)).2 W.isOpenImmersion.1,
      (isOpenImmersion_changeBaseHom_iff B S S' hS hS' g
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic).hom).2 W.isOpenImmersion.2⟩

/-- **An open substack over `S'` of Construction A is an open substack over `S`**, with the same
property of objects. -/
def OpenSubstack.ofChangeBase {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack (changeBaseAlgebraicStack B S S' hS hS' g 𝒳)) : OpenSubstack 𝒳 where
  property := W.property
  strictlyFull := W.strictlyFull
  isAlgebraic := (isAlgebraicStack_changeBase_iff B S S' hS hS' g
    (fullSubcategoryBased 𝒳 W.property)).1 W.isAlgebraic
  isOpenImmersion :=
    ⟨(isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
        (fullSubcategoryBasedInclusion 𝒳 W.property)).1 W.isOpenImmersion.1,
      (isOpenImmersion_changeBaseHom_iff B S S' hS hS' g
        (fullSubcategoryInclusion 𝒳 W.property
          ((isAlgebraicStack_changeBase_iff B S S' hS hS' g
            (fullSubcategoryBased 𝒳 W.property)).1 W.isAlgebraic)).hom).1
        W.isOpenImmersion.2⟩

/-! ### Smoothness of the structure morphism across Construction A -/

/-- The 1-morphism of Construction A of `𝒳` to the algebraic stack represented by `S/S'`, as a
1-morphism of algebraic stacks over `S'`. -/
abbrev changeBaseStructureMorphism (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    changeBaseAlgebraicStack B S S' hS hS' g 𝒳 ⟶ schemeStack.{u, w} B S' hS' (Over.mk g) :=
  Bicategory.InducedBicategory.mkHom (changeBaseStructureHom B S S' hS hS' g 𝒳)

/-- **A 1-morphism between the algebraic stacks of two schemes is smooth exactly when its
morphism of the site is.** Stacks 06FM for representable source and target. -/
theorem isSmooth_iff_smooth_baseMapOfBasedFunctor {W U : BigFppfOver B S hS}
    (q : schemeStack.{u, w} B S hS W ⟶ schemeStack.{u, w} B S hS U) :
    AlgebraicStacks.IsSmooth B S hS q ↔
      Smooth ((BigFppfOver.toScheme B S hS).map (baseMapOfBasedFunctor B S hS q.hom.hom)) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (schemeStack.{u, w} B S hS W).property
    (schemeStack.{u, w} B S hS U).property
    (yoneda.obj W) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) q.hom).trans
    ((Iff.of_eq (congrArg (Space.IsSmooth B S hS)
      (representingMap_eq_yoneda_map_baseMap B S hS q.hom.hom))).trans
      (Space.isSmooth_yoneda_map_iff B S hS _))

/-- Precomposing with an isomorphism does not change smoothness of a morphism of schemes. -/
theorem smooth_iso_comp_iff {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (k : Y ⟶ Z) :
    Smooth (e ≫ k) ↔ Smooth k := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  rw [← IsIso.inv_hom_id_assoc e k]
  infer_instance

/-- Precomposing with an `eqToHom` does not change smoothness of the underlying morphism of
schemes. -/
theorem smooth_toScheme_map_eqToHom_comp_iff {X Y Z : BigFppfOver B S hS} (h : X = Y)
    (k : Y ⟶ Z) :
    Smooth ((BigFppfOver.toScheme B S hS).map (eqToHom h ≫ k)) ↔
      Smooth ((BigFppfOver.toScheme B S hS).map k) := by
  subst h
  simp

/-- A 1-morphism is smooth exactly when its composite with a smooth surjective representable
1-morphism into its source is. -/
private theorem isSmooth_iff_isSmooth_comp_of_relative (S : Scheme.{u}) (hS : B.Contains S)
    {𝒲 𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (a : 𝒲 ⟶ 𝒱) (b : 𝒱 ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (hsm : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      a.hom hrep)
    (hsu : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      a.hom hrep) :
    AlgebraicStacks.IsSmooth B S hS b ↔ AlgebraicStacks.IsSmooth B S hS (a ≫ b) := by
  have ha : AlgebraicStacks.IsSmooth B S hS a :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒱.property _ hrep hsm
  exact ⟨AlgebraicStacks.isSmooth_comp B S hS a _ ha,
    AlgebraicStacks.isSmooth_of_comp_surjective B S hS a _ hrep ha
      ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ hrep).mpr hsu)⟩

/-- **The structure morphism `𝒳 ⟶ S` is smooth exactly when `𝒳 ⟶ S/S'` is smooth over `S'`.**
Both are read on a smooth surjective presentation of `𝒳` by a scheme `U` over `S`, pushed forward
to `S'` by Construction A: each composite is the 1-morphism of scheme stacks named by `U ⟶ S`,
smooth exactly when that morphism of schemes is. -/
theorem isSmooth_structureMorphism_iff_changeBase (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsSmooth B S hS (structureMorphism B S hS 𝒳) ↔
      AlgebraicStacks.IsSmooth B S' hS' (changeBaseStructureMorphism B S S' hS hS' g 𝒳) := by
  classical
  obtain ⟨hfib, ⟨hstack, -⟩, hdiag, U, f, hrep, hprop⟩ := 𝒳.property
  -- the presentation over `S`
  let a : schemeStack.{u, w} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom f)
  -- the presentation over `S'`
  have hrepb : IsRepresentableByAlgebraicSpaces B S' hS'
      (changeBaseFunctor B S S' hS hS' g f) :=
    (isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g f).2 hrep
  have hrep' : IsRepresentableByAlgebraicSpaces B S' hS'
      (BasedFunctor.comp (factorSliceInverse B S S' hS hS' g U)
        (changeBaseFunctor B S S' hS hS' g f)) :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S' hS'
      (𝒳' := schemeFibredCategory B S' hS' ((Over.map g).obj U))
      (𝒳 := changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS U))
      (𝒴 := changeBaseFiberedInGroupoids B S S' hS hS' g
        (CatFiberedInGroupoids.mk 𝒳.val.val hfib))
      (changeBaseFunctor B S S' hS hS' g f) _
      (factorSliceInverse B S S' hS hS' g U) (Iso.refl _)).1 hrepb
  have _ : (Space.surjectiveMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  have _ : (Space.smoothMorphismProperty B S' hS').IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S' hS') := inferInstance
  let 𝒳b := changeBaseFiberedInGroupoids B S S' hS hS' g (CatFiberedInGroupoids.mk 𝒳.val.val hfib)
  let bId : 𝒳b.val ⥤ᵇ 𝒳b.val := BasedFunctor.id 𝒳b.val
  have _ : Functor.IsEquivalence bId.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳b.val.obj))
  let fh : schemeFibredCategory B S hS U ⟶ CatFiberedInGroupoids.mk 𝒳.val.val hfib :=
    Bicategory.InducedBicategory.mkHom f
  let fprime : schemeFibredCategory B S' hS' ((Over.map g).obj U) ⟶ 𝒳b :=
    Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp (factorSliceInverse B S S' hS hS' g U)
        (changeBaseFunctor B S S' hS hS' g f))
  have transfer : ∀ (P : MorphismProperty (AlgebraicSpaces B S' hS'))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S' hS')],
      HasRelativeProperty.{u, u, u + 1, u} B S' hS' P (changeBaseHom B S S' hS hS' g fh) hrepb →
        HasRelativeProperty.{u, u, u + 1, u} B S' hS' P fprime hrep' := fun P _ _ h =>
    (hasRelativeProperty_iff_of_equivalences B S' hS' P fprime
      (changeBaseHom B S S' hS hS' g fh) (factorSliceInverse B S S' hS hS' g U) bId
      (Iso.refl _) hrepb).1 h
  let 𝒳' := changeBaseAlgebraicStack B S S' hS hS' g 𝒳
  let a' : schemeStack.{u, w} B S' hS' ((Over.map g).obj U) ⟶ 𝒳' :=
    Bicategory.InducedBicategory.mkHom fprime
  -- both sides are smoothness of `U ⟶ S`
  have hleft : AlgebraicStacks.IsSmooth B S hS (structureMorphism B S hS 𝒳) ↔
      Smooth (B.inclusion.map U.hom) := by
    rw [← isSmooth_structureMorphism_schemeStack_iff, ← comp_structureMorphism B S hS a]
    exact isSmooth_iff_isSmooth_comp_of_relative B S hS a _ hrep
      (fun V y hy G hG he => (hprop V y hy G hG he).2)
      (fun V y hy G hG he => (hprop V y hy G hG he).1)
  have hright : AlgebraicStacks.IsSmooth B S' hS'
      (changeBaseStructureMorphism B S S' hS hS' g 𝒳) ↔ Smooth (B.inclusion.map U.hom) := by
    have hcomp : AlgebraicStacks.IsSmooth B S' hS'
        (a' ≫ changeBaseStructureMorphism B S S' hS hS' g 𝒳) ↔
          Smooth (B.inclusion.map U.hom) := by
      rw [isSmooth_iff_smooth_baseMapOfBasedFunctor, baseMapOfBasedFunctor]
      refine (smooth_toScheme_map_eqToHom_comp_iff B S' hS' _ _).trans ?_
      let Y : Over U := (Over.iteratedSliceBackward U).obj
        ((Over.iteratedSliceForward ((Over.map g).obj U)).obj (Over.mk (𝟙 _)))
      have hY : 𝒳.val.val.p.obj (f.obj Y) = (Over.forget U).obj Y := Functor.congr_obj f.w Y
      show Smooth (B.inclusion.map (𝒳.val.val.p.obj (f.obj Y)).hom) ↔ _
      rw [hY]
      show Smooth (B.inclusion.map (𝟙 _ ≫ U.hom)) ↔ _
      rw [Category.id_comp]
    rw [← hcomp]
    exact isSmooth_iff_isSmooth_comp_of_relative B S' hS' a' _ hrep'
      (transfer _ ((hasRelativeProperty_smooth_changeBaseHom_iff.{u, u, u + 1} B S S' hS hS' g
        (@AlgebraicGeometry.Smooth.{u}) fh hrep).2
          (fun T z hz G hG hE => (hprop T z hz G hG hE).2)))
      (transfer _ ((hasRelativeProperty_surjective_changeBaseHom_iff.{u, u, u + 1, u} B S S' hS
        hS' g fh hrep).2 (fun T z hz G hG hE => (hprop T z hz G hG hE).1)))
  exact hleft.trans hright.symm

/-- **Smoothness on an open substack is unchanged by Construction A.** For an open substack `V`
of `𝒳`, the structure morphism restricted to `V` is smooth over `S` exactly when the 1-morphism
to `S/S'` restricted to `V`, viewed over `S'`, is smooth over `S'`. -/
theorem isSmooth_inclusion_comp_structureMorphism_iff_changeBase
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : OpenSubstack 𝒳) :
    AlgebraicStacks.IsSmooth B S hS
        (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic ≫ structureMorphism B S hS 𝒳) ↔
      AlgebraicStacks.IsSmooth B S' hS'
        (fullSubcategoryInclusion _ (V.changeBase B S S' hS hS' g).property
            (V.changeBase B S S' hS hS' g).isAlgebraic ≫
          changeBaseStructureMorphism B S S' hS hS' g 𝒳) := by
  rw [comp_structureMorphism]
  exact isSmooth_structureMorphism_iff_changeBase B S S' hS hS' g
    (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic)

/-- **The smooth locus of the structure morphism is unchanged by Construction A.** Let `𝒳` be an
algebraic stack over `S` and `g : S ⟶ S'`. The smooth locus (Stacks 0DZR) of `𝒳 ⟶ S` and the
smooth locus over `S'` of the 1-morphism `𝒳 ⟶ S/S'` of Construction A (Stacks 04X5) have the
same objects. -/
theorem IsSmoothLocus.property_eq_changeBase {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS (structureMorphism B S hS 𝒳) W)
    {W' : OpenSubstack (changeBaseAlgebraicStack B S S' hS hS' g 𝒳)}
    (hW' : IsSmoothLocus B S' hS' (changeBaseStructureMorphism B S S' hS hS' g 𝒳) W') :
    W.property = W'.property :=
  le_antisymm
    (hW'.2 (W.changeBase B S S' hS hS' g)
      ((isSmooth_inclusion_comp_structureMorphism_iff_changeBase B S S' hS hS' g W).1 hW.1))
    (hW.2 (W'.ofChangeBase B S S' hS hS' g)
      ((isSmooth_inclusion_comp_structureMorphism_iff_changeBase B S S' hS hS' g
        (W'.ofChangeBase B S S' hS hS' g)).2 hW'.1))

end Stack

end AlgebraicGeometry

end

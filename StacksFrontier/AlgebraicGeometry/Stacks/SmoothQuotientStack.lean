module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.FppfPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# Smoothness of a quotient stack over the base: the descent step

Let `X ⟶ Y` be a smooth morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`G` be a group algebraic space over `Y` which is flat and locally of finite presentation over
`Y`, and let `G` act on `X` over `Y`. **Stacks 0DLS** says that the quotient stack `[X/G]` is
smooth over `Y`. The source's proof descends smoothness along the atlas `X ⟶ [X/G]`, which is
surjective, flat and locally of finite presentation by Stacks 06FH; the descent itself is
Stacks 0AHE for morphisms of algebraic spaces. This file proves the descent step and the
identification of Stacks 044R that it needs; the atlas properties of Stacks 06FH are
`AlgebraicGeometry.Stack.quotientModelAtlasFppf`, and Stacks 0DLS itself is
`AlgebraicGeometry.Stack.isSmooth_quotientStackModelToBase`.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackModelToBaseOfGroupoid` and
  `AlgebraicGeometry.Stack.quotientStackModelToBase`: the canonical morphism `[U/R] ⟶ A` of
  Stacks 044R, read on a model of the quotient stack, for a groupoid and for a group action.
* `AlgebraicGeometry.Stack.quotientStackModelProjection`: the atlas `U ⟶ [U/R]` read on a model.
* `AlgebraicGeometry.Stack.QuotientModelAtlasFppf`: the four properties of that atlas which
  Stacks 06FH asserts.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_of_fppf`: in a composable pair
  `f : 𝒳 ⟶ 𝒴`, `g : 𝒴 ⟶ 𝒵` of 1-morphisms of algebraic stacks over `S` with `f` representable
  by algebraic spaces, surjective, flat and locally of finite presentation, smoothness of
  `f ≫ g` implies smoothness of `g`.
* `AlgebraicGeometry.Stack.representingMap_quotientStackModelProjection_comp`: **Stacks 044R**
  through a model — the composite of the atlas and the morphism to the base induces the structure
  morphism of the object space.
* `AlgebraicGeometry.Stack.isSmooth_quotientStackModelToBaseOfGroupoid`: the descent of the
  smoothness of `U ⟶ A` along an atlas with the four properties of Stacks 06FH.

## Implementation notes

The explicit stackification of Stacks 044Q has its morphisms one universe above the morphisms of
the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks`, which is where smoothness of a
1-morphism of algebraic stacks (Stacks 075U) is defined. So the quotient stack is presented by a
*model*: an object `𝒳` of `AlgebraicGeometry.Stack.AlgebraicStacks` together with an equivalence
over the big fppf site between the structure functor of `[X/G]` and that of `𝒳`. Algebraicity and
smoothness are invariant under equivalence over the site, so smoothness at every model is the
source's claim; that `[X/G]` is algebraic, so that a model exists, is Stacks 06FI.

The descent of smoothness along an fppf 1-morphism of algebraic stacks has as its engine
Stacks 0AHE (`AlgebraicGeometry.Space.isSmooth_of_comp_of_fppf`), read on the algebraic-space
base changes of the three properties of the atlas; its shape follows that of Stacks 06U8 for
local finite type, `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0AHE](https://stacks.math.columbia.edu/tag/0AHE)
* [Stacks Project, Tag 0DLS](https://stacks.math.columbia.edu/tag/0DLS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The fppf descent of smoothness for 1-morphisms of algebraic stacks over `S`.** Let
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If `f ≫ g` is smooth
and `f` is representable by algebraic spaces, surjective, flat and locally of finite
presentation, then `g` is smooth.

The space-level input is Stacks 0AHE, and the three properties of `f` are read on its
algebraic-space base changes through Stacks 04XC. This is the smooth analogue of Stacks 06U8,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`. -/
theorem isSmooth_of_comp_of_fppf
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsSmooth B S hS (f ≫ g))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hfsurj : IsSurjective B S hS f)
    (hfflat : IsFlat B S hS f)
    (hflfp : IsLocallyOfFinitePresentation B S hS f) :
    IsSmooth B S hS g := by
  let iflat1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let iflat2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let ilfp1 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let ilfp2 : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hsurjRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f.hom hf :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS f.hom hf).1
      (isSurjectiveOnObjects_of_pointsMap_surjective B S hS f hfsurj)
  have hflatRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ k => Space.IsFlat B S hS k)) f.hom hf :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hf hfflat
  have hlfpRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS
        (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)) f.hom hf :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f.hom hf
      (hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
        𝒳.property 𝒴.property f.hom hflfp)
  refine hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
    𝒴.property 𝒵.property g.hom ?_
  refine hasPropertyOnEverySmoothDiagram_of_comp_of_fppf B S hS _ ?_ f.hom g.hom hf ?_
    (hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) (f ≫ g).hom hfg)
  · intro X' Y' Z' hX' hY' hZ' p c hps hpf hpl hpc
    exact Space.isSmooth_of_comp_of_fppf B S hS hX' hY' hZ' p (p ≫ c) c rfl hps hpf hpl hpc
  · intro V' hV' k N hN U' hU' eU'
    exact ⟨prop_representingMap_of_hasRelativeProperty B S hS
        (Space.surjectiveMorphismProperty B S hS) f.hom hf hsurjRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      prop_representingMap_of_hasRelativeProperty B S hS _ f.hom hf hflatRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      prop_representingMap_of_hasRelativeProperty B S hS _ f.hom hf hlfpRel
        (fibredCategory B S hS V') k N hN U' V' hU' hV' eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _)⟩

end AlgebraicStacks

/-- The action groupoid of `G` acting on `X` over `Y`, as given by Stacks 0444. Its quotient
stack is the quotient stack `[X/G]` of Stacks 044Q, part (2). -/
noncomputable abbrev actionGroupoid (Y : AlgebraicSpaces B S hS) (G X : Over Y.obj)
    [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left) :
    GroupoidInAlgebraicSpaces B S hS Y :=
  (Space.groupoidOfAction Y G X hG hX).groupoid

/-- **The canonical morphism `[X/G] ⟶ Y` of Stacks 044R, read on a model of the quotient
stack**: the structure arrow of the quotient stack of the action groupoid, transported along an
equivalence over the big fppf site with an object of the 2-category of algebraic stacks. -/
noncomputable def quotientStackModelToBase
    (Y : AlgebraicSpaces B S hS) (G X : Over Y.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (actionGroupoid B S hS Y G X hG hX)).p 𝒳.val.val.p) :
    𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := e.inv.functor ⋙
        (quotientStackToBase (actionGroupoid B S hS Y G X hG hX)).toFunctor
      w := by
        rw [Functor.assoc, (quotientStackToBase (actionGroupoid B S hS Y G X hG hX)).w,
          e.inv.w] })

end AlgebraicGeometry.Stack

end

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The canonical morphism `[U/R] ⟶ A` of Stacks 044R, read on a model of the quotient stack**
of an arbitrary groupoid in algebraic spaces over an algebraic space `A`. -/
noncomputable def quotientStackModelToBaseOfGroupoid
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒳.val.val.p) :
    𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS A.obj A.property :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := e.inv.functor ⋙ (quotientStackToBase H).toFunctor
      w := by rw [Functor.assoc, (quotientStackToBase H).w, e.inv.w] })

/-- **The atlas `U ⟶ [U/R]` of Stacks 044R, read on a model of the quotient stack**: the
canonical projection of the object space followed by the equivalence onto the model. -/
noncomputable def quotientStackModelProjection
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒳.val.val.p) :
    algebraicSpaceStack.{u, w} B S hS H.objects.obj H.objects.property ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (quotientStackProjection H).toFunctor ⋙ e.hom.functor
      w := by rw [Functor.assoc, e.hom.w, (quotientStackProjection H).w] })

/-- **Stacks 044R through a model of the quotient stack.** The composite
`U ⟶ [U/R] ⟶ A` of the atlas and the canonical morphism to the base induces, on representing
presheaves, the structure morphism `U ⟶ A` of the object space of the groupoid. -/
theorem representingMap_quotientStackModelProjection_comp
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒳.val.val.p) :
    representingMap B S hS
        (algebraicSpaceStack.{u, w} B S hS H.objects.obj H.objects.property).val
        (algebraicSpaceStack.{u, w} B S hS A.obj A.property).val
        H.objects.obj A.obj
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e ≫
          quotientStackModelToBaseOfGroupoid.{u, w} B S hS A H 𝒳 e).hom =
      H.objectsToBase.hom := by
  have hbase : (associatedMap B S hS H.objectsToBase.hom).1.hom =
      BasedFunctor.comp (quotientStackProjection H) (quotientStackToBase H) :=
    (quotientStackProjection_comp_toBase H).symm
  have hα : ∀ x : (algebraicSpaceStack.{u, w} B S hS
        H.objects.obj H.objects.property).val.val.obj,
      (algebraicSpaceStack.{u, w} B S hS A.obj A.property).val.val.p.IsHomLift
        (𝟙 ((algebraicSpaceStack.{u, w} B S hS
          H.objects.obj H.objects.property).val.val.p.obj x))
        ((quotientStackToBase H).toFunctor.map
          (e.unitIso.inv.app ((quotientStackProjection H).obj x))) := by
    intro x
    have hlift : (quotientStack H).p.IsHomLift
        (𝟙 ((quotientStack H).p.obj ((quotientStackProjection H).obj x)))
        (e.unitIso.inv.app ((quotientStackProjection H).obj x)) :=
      e.isHomLift_unitIso_inv_app _
    have h2 := BasedFunctor.preserves_isHomLift (quotientStackToBase H)
      (𝟙 ((quotientStack H).p.obj ((quotientStackProjection H).obj x)))
      (e.unitIso.inv.app ((quotientStackProjection H).obj x))
    rw [← BasedFunctor.w_obj (quotientStackProjection H) x]
    exact h2
  refine Eq.trans ?_
    (representingMap_associatedMap B S hS H.objects.obj A.obj H.objectsToBase.hom)
  refine representingMap_congr_twoIso B S hS H.objects.obj A.obj _ _ ?_
  refine Bicategory.InducedBicategory.isoMk ?_
  rw [hbase]
  exact BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft (quotientStackProjection H).toFunctor
      (Functor.isoWhiskerRight e.unitIso.symm (quotientStackToBase H).toFunctor)) hα

/-- **The four properties of the atlas of a model which Stacks 06FH asserts**: the atlas
`U ⟶ [U/R]` of Stacks 044R, read on a model of the quotient stack, is representable by algebraic
spaces, surjective, flat and locally of finite presentation. When the source and the target of
the groupoid are flat and locally of finite presentation this holds, by
`AlgebraicGeometry.Stack.quotientModelAtlasFppf`. -/
abbrev QuotientModelAtlasFppf
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒳.val.val.p) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS
      (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e).hom.hom ∧
    IsSurjective B S hS (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e) ∧
    AlgebraicStacks.IsFlat B S hS (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e) ∧
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e)

/-- **The smoothness of a quotient stack over the base, for a groupoid in algebraic spaces.** If
the structure morphism `U ⟶ A` of the object space is smooth and the atlas `U ⟶ [U/R]` is
representable by algebraic spaces, surjective, flat and locally of finite presentation, then the
canonical morphism `[U/R] ⟶ A` of Stacks 044R is a smooth 1-morphism of algebraic stacks.

The identification of Stacks 044R of the composite `U ⟶ [U/R] ⟶ A` is discharged by
`AlgebraicGeometry.Stack.representingMap_quotientStackModelProjection_comp`, and the descent of
smoothness along the atlas is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_comp_of_fppf`. -/
theorem isSmooth_quotientStackModelToBaseOfGroupoid
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (hsmooth : Space.IsSmooth B S hS H.objectsToBase.hom)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒳.val.val.p)
    (hatlas : QuotientModelAtlasFppf.{u, w} B S hS A H 𝒳 e) :
    AlgebraicStacks.IsSmooth B S hS
      (quotientStackModelToBaseOfGroupoid.{u, w} B S hS A H 𝒳 e) := by
  obtain ⟨hrep, hsurj, hflat, hlfp⟩ := hatlas
  refine AlgebraicStacks.isSmooth_of_comp_of_fppf B S hS
    (quotientStackModelProjection.{u, w} B S hS A H 𝒳 e) _ ?_ hrep hsurj hflat hlfp
  refine isSmooth_of_isSmooth_representingMap B S hS H.objects.obj A.obj
    H.objects.property A.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ ?_
  rw [representingMap_quotientStackModelProjection_comp B S hS A H 𝒳 e]
  exact hsmooth

/-- The canonical morphism `[X/G] ⟶ Y` of Stacks 044R read on a model of `[X/G]` is the one of
the action groupoid of Stacks 0444. -/
theorem quotientStackModelToBase_eq
    (Y : AlgebraicSpaces B S hS) (G X : Over Y.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (actionGroupoid B S hS Y G X hG hX)).p 𝒳.val.val.p) :
    quotientStackModelToBase.{u, w} B S hS Y G X hG hX 𝒳 e =
      quotientStackModelToBaseOfGroupoid.{u, w} B S hS Y
        (actionGroupoid B S hS Y G X hG hX) 𝒳 e :=
  rfl

end AlgebraicGeometry.Stack

end

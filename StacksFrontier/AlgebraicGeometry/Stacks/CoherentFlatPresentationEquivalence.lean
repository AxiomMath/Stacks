module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentPresentationEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EquivalenceOverQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackQuasicoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# Coherent modules on a locally Noetherian algebraic stack and on a flat presentation (Stacks 0GRC)

Let `𝒳` be a locally Noetherian algebraic stack, let `U` be an algebraic space and let
`f : U → 𝒳` be surjective, locally of finite presentation and flat.  Let `(U, R, s, t, c)` be the
groupoid in algebraic spaces of Stacks 04T4, with `R` an algebraic space representing
`U ×_𝒳 U` (which exists by Stacks 04T4 (1)), and `f_can : [U/R] → 𝒳` the isomorphism of
Stacks 04WY.  Sheaves on Stacks, Section 06WU, and Stacks 06WT give equivalences

`QCoh(𝒪_𝒳) ≅ QCoh(𝒪_{[U/R]}) ≅ QCoh(U, R, s, t, c)`,

and Stacks 0GRC says that their composite sends coherent modules to coherent modules and vice
versa, so that it induces `Coh(𝒪_𝒳) ≅ Coh(U, R, s, t, c)`.

This file constructs that composite and runs
`AlgebraicGeometry.Stack.coherentPresentationEquivalence` at it.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.hasCoverProperties_of_flat`: the hypothesis of
  Stacks 04WY — every algebraic space representing a base change of `f` along a scheme-valued
  point of `𝒳` is surjective, flat and locally of finite presentation over the scheme — from `f`
  surjective, flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.SelfIntersection.quasicoherentFlatPresentationEquivalence`:
  `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`, the composite of the inverse image along `f_can` and the
  equivalence of Stacks 06WT.
* `AlgebraicGeometry.Stack.SelfIntersection.coherentFlatPresentationEquivalence`: **Stacks 0GRC**,
  `Coh(𝒪_𝒳) ≌ Coh(U, R, s, t, c)`.

## References

* [Stacks Project, Tag 0GRC](https://stacks.math.columbia.edu/tag/0GRC)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 06WU](https://stacks.math.columbia.edu/tag/06WU)
-/

@[expose] public section

open CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack.SelfIntersection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, t} B S hS)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳)

/-- **The hypothesis of Stacks 04WY from a surjective, flat, locally finitely presented chart.**
If `f : U → 𝒳` is surjective, flat and locally of finite presentation, then every algebraic space
representing a base change of `f` along a scheme-valued point `T → 𝒳` is surjective, flat and
locally of finite presentation over `T`: a 1-morphism from an algebraic space to an algebraic
stack is representable by algebraic spaces, and for such a 1-morphism each of the three
properties is the relative property of Stacks 03YK (Stacks 04XI for surjectivity, Stacks 06FM for
flatness and local finite presentation). -/
theorem hasCoverProperties_of_flat
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f) :
    ∀ (T : BigFppfOver B S hS)
        (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
        (_hy : y ⋙ 𝒳.val.val.p = Over.map T.hom)
        (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hG : IsAlgebraicSpace B T.left.1 T.left.2 G),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom)
            (algebraicSpaceStack.{u, t} B S hS F hF).val.val.p 𝒳.val.val.p y
            (CatFiberedInGroupoids.homFunctor f.hom))
          (presheafOfCategories (G ⋙ typeToCat)).p) →
        let a := algebraicSpaceMap B S hS T
          ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨G, hG⟩)
        (Space.IsSurjective B S hS a.hom ∧ Space.IsFlat B S hS a.hom ∧
          Space.IsLocallyOfFinitePresentation B S hS a.hom) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) f.hom
  let flatP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsFlat B S hS h
  let lfpP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h
  let : (spaceProperty B S hS flatP).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.isFlat_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS flatP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  let : (spaceProperty B S hS lfpP).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS lfpP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hrelSurj :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, t, u + 1} B S hS f hrep).mp hsurj
  have hrelFlat := hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS flatP
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom hrep hflat
  have hrelLfp := hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS lfpP
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) f.hom hrep
    ((hasPropertyOnEverySmoothDiagram_iff_some.{u, t} B S hS lfpP
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (algebraicSpaceStack.{u, t} B S hS F hF).property 𝒳.property f.hom).1 hlfp)
  intro T y hy G hG he
  exact ⟨hrelSurj T y hy G hG he, hrelFlat T y hy G hG he, hrelLfp T y hy G hG he⟩

/-- The algebraic space `R` representing the relation `U ×_𝒳 U`, chosen by Stacks 04T4 (1). -/
noncomputable def flatPresentationRelation : AlgebraicSpaces B S hS :=
  ⟨(isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, t} B S hS F hF).val 𝒳.val f.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)).choose,
    (isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, t} B S hS F hF).val 𝒳.val f.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)).choose_spec.1⟩

/-- The chosen identification of `U ×_𝒳 U` with the algebraic space
`AlgebraicGeometry.Stack.SelfIntersection.flatPresentationRelation`. -/
noncomputable def flatPresentationRelationEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (relation B S hS (algebraicSpaceStack.{u, t} B S hS F hF).val 𝒳.val f.hom.hom).val.p
      (presheafOfCategories ((flatPresentationRelation B S hS 𝒳 F hF f).obj ⋙ typeToCat)).p :=
  Classical.choice (isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (algebraicSpaceStack.{u, t} B S hS F hF).val 𝒳.val f.hom.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)).choose_spec.2

/-- **The presentation datum of Stacks 04T4 (4) and (5)** of `𝒳` attached to `f : U → 𝒳`: the
groupoid `(U, R, s, t, c)` with `R` the chosen algebraic space representing `U ×_𝒳 U`, and the
canonical morphism `f_can : [U/R] → 𝒳`. -/
noncomputable abbrev flatPresentation :=
  selfIntersectionPresentation (U := ⟨F, hF⟩) (R := flatPresentationRelation B S hS 𝒳 F hF f)
    (StacksRepresentableCFG.EquivalenceOver.refl
      (fibredCategory B S hS F).val.p)
    (flatPresentationRelationEquivalence B S hS 𝒳 F hF f) 𝒳.property

/-- The groupoid in algebraic spaces `(U, R, s, t, c)` of Stacks 04T4 attached to `f : U → 𝒳`. -/
noncomputable abbrev flatPresentationGroupoid :=
  (flatPresentation B S hS 𝒳 F hF f).groupoid

/-- **`f_can : [U/R] → 𝒳` is an equivalence over the site** (Stacks 04WY), when `f` is
surjective, flat and locally of finite presentation: a chosen quasi-inverse over the site, with
vertical unit and counit. -/
noncomputable def flatPresentationEquivalenceOver
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f) :
    Functor.IsEquivalenceOver (quotientStack (flatPresentationGroupoid B S hS 𝒳 F hF f)).p
      𝒳.val.val.p (flatPresentation B S hS 𝒳 F hF f).canonicalMap.toFunctor :=
  Classical.choice (nonempty_isEquivalenceOver_canonicalMap (U := ⟨F, hF⟩)
    (R := flatPresentationRelation B S hS 𝒳 F hF f)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS F).val.p)
    (flatPresentationRelationEquivalence B S hS 𝒳 F hF f) 𝒳.property
    (hasCoverProperties_of_flat B S hS 𝒳 F hF f hlfp hflat hsurj))

/-- **`QCoh(𝒪_𝒳) ≌ QCoh(𝒪_{[U/R]})`**: the inverse image along the equivalence
`f_can : [U/R] → 𝒳` of Stacks 04WY, as in Sheaves on Stacks, Section 06WU. -/
noncomputable def quasicoherentQuotientStackEquivalence
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids ≌
      FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} B S hS
        (quotientStack (flatPresentationGroupoid B S hS 𝒳 F hF f)).p
        (isFiberedInGroupoids_quotientStack _) :=
  let E := flatPresentationEquivalenceOver B S hS 𝒳 F hF f hlfp hflat hsurj
  let e := CategoryTheory.Equivalence.mk _ E.inv E.unitIso.symm E.counitIso
  haveI : (flatPresentation B S hS 𝒳 F hF f).canonicalMap.toFunctor.IsEquivalence :=
    e.isEquivalence_functor
  haveI : E.inv.IsEquivalence := e.symm.isEquivalence_functor
  FibredEquivalence.quasicoherentEquivalence
    (quotientStack (flatPresentationGroupoid B S hS 𝒳 F hF f)).p 𝒳.val.val.p
    (isFiberedInGroupoids_quotientStack _) 𝒳.val.isFiberedInGroupoids
    (flatPresentation B S hS 𝒳 F hF f).canonicalMap.toFunctor
    (flatPresentation B S hS 𝒳 F hF f).canonicalMap.w E.inv E.inv_over E.counitIso
    E.counit_vertical

/-- **`QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`**: the inverse image along the equivalence
`f_can : [U/R] → 𝒳` (Sheaves on Stacks, Section 06WU), followed by the equivalence
`QCoh(𝒪_{[U/R]}) ≌ QCoh(U, R, s, t, c)` of Stacks 06WT. -/
noncomputable def quasicoherentFlatPresentationEquivalence
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f) :
    quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ≌
      Space.QuasicoherentModule B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f) :=
  (quasicoherentQuotientStackEquivalence B S hS 𝒳 F hF f hlfp hflat hsurj).trans
    (quotientStackQuasicoherentEquivalence (flatPresentationGroupoid B S hS 𝒳 F hF f))

/-- **The forward functor of `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` is `ℱ ↦ f^*ℱ|_{U_étale}`** on
underlying `𝒪_U`-modules, up to isomorphism: it is `x^*(f_can^*ℱ)|_{U_étale}` for the projection
`x : U → [U/R]`, and the 2-isomorphism `f_can ∘ x ≅ f` of Stacks 04T4 is vertical. -/
theorem nonempty_quasicoherentFlatPresentationEquivalence_functor_obj_iso
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (ℱ : quasicoherentModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :
    Nonempty ((((quasicoherentFlatPresentationEquivalence B S hS 𝒳 F hF f hlfp hflat
        hsurj).functor.obj ℱ).F.obj) ≅ spaceChartRestriction B S hS 𝒳 F hF f ℱ.obj) := by
  let P := flatPresentation B S hS 𝒳 F hF f
  let α : quotientStackProj (flatPresentationGroupoid B S hS 𝒳 F hF f) ⋙
      P.canonicalMap.toFunctor ≅ CatFiberedInGroupoids.homFunctor f.hom := P.extends_f.1
  exact FibredEquivalence.nonempty_iso_etaleRestrictedModuleInverseImage (U := ⟨F, hF⟩)
    (quotientStack (flatPresentationGroupoid B S hS 𝒳 F hF f)).p 𝒳.val.val.p
    (isFiberedInGroupoids_quotientStack (flatPresentationGroupoid B S hS 𝒳 F hF f))
    𝒳.val.isFiberedInGroupoids P.canonicalMap.toFunctor (fibredCategory B S hS F).val.p
    (fibredCategory B S hS F).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory B S hS F).val.p)
    P.canonicalMap.w (quotientStackProj (flatPresentationGroupoid B S hS 𝒳 F hF f))
    (isFibredOneMorphism_quotientStackProj (flatPresentationGroupoid B S hS 𝒳 F hF f))
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) α P.extends_f.2 ℱ.obj

/-- **Stacks 0GRC.** Let `𝒳` be a locally Noetherian algebraic stack, let `U` be an algebraic
space and let `f : U → 𝒳` be surjective, locally of finite presentation and flat.  Let
`(U, R, s, t, c)` be the groupoid in algebraic spaces of Stacks 04T4, `R` representing
`U ×_𝒳 U`.  Then the equivalence `QCoh(𝒪_𝒳) ≅ QCoh(𝒪_{[U/R]}) ≅ QCoh(U, R, s, t, c)` of Sheaves
on Stacks, Section 06WU, and Stacks 06WT
(`AlgebraicGeometry.Stack.SelfIntersection.quasicoherentFlatPresentationEquivalence`) sends
coherent modules to coherent modules and vice versa, i.e. induces an equivalence
`Coh(𝒪_𝒳) ≅ Coh(U, R, s, t, c)`.

`Coh(𝒪_𝒳)` is the category of coherent modules of Stacks 0GR6 and `Coh(U, R, s, t, c)` that of
Groupoids in Spaces, Section 0GPN.  The equivalence is the restriction of
`quasicoherentFlatPresentationEquivalence` to these full subcategories, by
`AlgebraicGeometry.Stack.coherentPresentationEquivalence`. -/
@[stacks 0GRC]
noncomputable def coherentFlatPresentationEquivalence
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f) :
    Coh.{u, u, t} B S hS 𝒳 ≌
      Space.QuasicoherentModule.Coh B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f) :=
  coherentPresentationEquivalence B S hS 𝒳 (flatPresentationGroupoid B S hS 𝒳 F hF f) h𝒳 f
    hlfp hflat hsurj (quasicoherentFlatPresentationEquivalence B S hS 𝒳 F hF f hlfp hflat hsurj)
    (fun ℱ => Classical.choice
      (nonempty_quasicoherentFlatPresentationEquivalence_functor_obj_iso B S hS 𝒳 F hF f hlfp
        hflat hsurj ℱ))

end AlgebraicGeometry.Stack.SelfIntersection

end
